-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctions_Quasi_quasi_l_proximity_theorem
-- name    : DiscreteConvex.LConvexFunctions.Quasi.quasi_l_proximity_theorem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T00:17:48.110664+00:00
-- url     : https://prove2.me/theorems/761d5ed1-27e3-44bb-b4ca-ddcecd1793b4
-- title:
--   Theorem 7.54 -- the quasi L-proximity theorem
-- statement:
--   **Theorem 7.54** (p.201). Let $g : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$ satisfy (SSQSB) and $g(p) = g(p+\mathbf 1)$ for all $p$, and assume $n=|V|$ and $\alpha \in \mathbb Z_{++}$. If $p_\alpha \in \operatorname{dom} g$ satisfies $g(p_\alpha) \le g(p_\alpha + \alpha\chi_Y)$ for all $Y \subseteq V$, then $\arg\min g \ne \emptyset$ and there is $p^* \in \arg\min g$ with the componentwise bound $p_\alpha \le p^* \le p_\alpha + (n-1)(\alpha-1)\mathbf 1$ — verbatim the same conclusion, and the same exact bound, as chunk 08's Theorem 7.18(1), now established for the strictly larger class of functions satisfying (SSQSB) rather than (SBF[Z]). This genuinely broadens the class covered by an explicit proximity guarantee to include every strictly increasing rescaling of an L-convex objective (Example 7.48), a class the plain L-convex theory of chunk 08 says nothing about.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.201, Theorem 7.54.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.201, Theorem 7.54

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctions_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctions_ArgMin
import Definitions.Def_DiscreteConvex_LConvexFunctions_IndicatorVec
import Definitions.Def_DiscreteConvex_LConvexFunctions_Quasi_SSQSB

open DiscreteConvex.LConvexFunctions

namespace DiscreteConvex.LConvexFunctions.Quasi

/-- Theorem 7.54, the quasi L-proximity theorem (Murota, *Discrete Convex Analysis*, SIAM 2003,
p.201). Let `g : Zⱽ → R ∪ {+∞}` satisfy (SSQSB) and `g(p) = g(p+1)` for all `p`, and assume
`n = |V|` and `α ∈ Z++`. If `pα ∈ dom g` satisfies `g(pα) ≤ g(pα + αχ_Y)` for all `Y ⊆ V`, then
`arg min g ≠ ∅` and there exists `p* ∈ arg min g` with `pα ≤ p* ≤ pα + (n-1)(α-1)·1`
(componentwise) — the same conclusion as Theorem 7.18(1) (chunk `08-lconvex-functions-i`), for
the strictly larger class of functions satisfying (SSQSB) rather than (SBF[Z]). -/
theorem quasi_l_proximity_theorem {V : Type*} [Fintype V] [DecidableEq V] (α : ℤ) (hα : 0 < α)
    (g : (V → ℤ) → WithTop ℝ) (hper : ∀ p : V → ℤ, g (fun v => p v + 1) = g p)
    (hg : SSQSB g) (pα : V → ℤ) (hpα : pα ∈ DomZ g)
    (hloc : ∀ Y : Finset V, g pα ≤ g (fun v => pα v + α * IndicatorVec Y v)) :
    (ArgMin g).Nonempty ∧ ∃ p ∈ ArgMin g, ∀ v : V,
      pα v ≤ p v ∧ p v ≤ pα v + ((Fintype.card V : ℤ) - 1) * (α - 1) := by sorry

end DiscreteConvex.LConvexFunctions.Quasi
