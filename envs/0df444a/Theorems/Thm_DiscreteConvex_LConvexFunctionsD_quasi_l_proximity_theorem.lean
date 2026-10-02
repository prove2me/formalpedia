-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsD_quasi_l_proximity_theorem
-- name    : DiscreteConvex.LConvexFunctionsD.quasi_l_proximity_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:03:07.094934+00:00
-- url     : https://prove2.me/theorems/94f5d970-fb17-45f0-9caf-e491e0bbd86b
-- title:
--   Theorem 7.54 -- quasi_l_proximity_theorem
-- statement:
--   **Theorem 7.54** (Quasi L-proximity theorem; p.201-202). Let $g:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$ satisfy (SSQSB) and $g(p)=g(p+\mathbf 1)$, $n=|V|$, $\alpha\in\mathbb Z_{++}$. If $p_\alpha\in\operatorname{dom} g$ satisfies $g(p_\alpha)\le g(p_\alpha+\alpha\chi_Y)$ for all $Y\subseteq V$, then $\arg\min g\ne\emptyset$ and some $p^*\in\arg\min g$ has $p_\alpha\le p^*\le p_\alpha+(n-1)(\alpha-1)\mathbf 1$.
--
--   **Not in this chunk's own `BRIEF.md` table, and its full statement spans one page beyond this chunk's nominal PDF range** (213-220): it opens on PDF220 but its inequality and constant are stated on PDF221, where chapter 7 itself ends (Bibliographical Notes follow, then Chapter 8 begins on PDF223). No later mission in this series covers chapter 7's remainder, so it is included here rather than left permanently unplaced — see `STATUS.md`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.201-202, Theorem 7.54.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.201-202, Theorem 7.54

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IndicatorVec
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ArgMin
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SSQSB

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.54 (Quasi L-proximity theorem; p.201-202, this theorem's statement spans into
PDF221, one page beyond this chunk's own nominal range — chapter 7 ends at PDF221 and no later
mission covers chapter 7, so it is included here; see `STATUS.md`). The proximity theorem for
L-convex functions generalizes to (SSQSB), 1-periodic functions. -/
theorem quasi_l_proximity_theorem (g : (V → ℤ) → WithTop ℝ) (hssqsb : SSQSB g)
    (hper : ∀ p : V → ℤ, g (p + 1) = g p) (alpha : ℤ) (halpha : 0 < alpha)
    (palpha : V → ℤ) (hpalpha : palpha ∈ DomZ g)
    (hcond : ∀ Y : Finset V, g palpha ≤ g (fun v => palpha v + alpha * IndicatorVec Y v)) :
    (ArgMin g).Nonempty ∧
      ∃ pstar ∈ ArgMin g, ∀ v : V,
        palpha v ≤ pstar v ∧ pstar v ≤ palpha v + ((Fintype.card V : ℤ) - 1) * (alpha - 1) := by sorry

end DiscreteConvex.LConvexFunctionsD
