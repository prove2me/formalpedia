-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsD_quasi_submodular_translation_inequalities
-- name    : DiscreteConvex.LConvexFunctionsD.quasi_submodular_translation_inequalities
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-28T01:03:55.52478+00:00
-- url     : https://prove2.me/theorems/94b7f3ef-4f95-4673-babe-06008f74fc76
-- title:
--   Proposition 7.50 -- quasi_submodular_translation_inequalities
-- statement:
--   **Proposition 7.50** (p.200). Assume $g:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$ satisfies $g(p)=g(p+\mathbf 1)$ for all $p$. (1) For $g$ satisfying (QSBw), $p,q\in\mathbb Z^V$, $\alpha\in\mathbb Z$: $\max\{g(p),g(q)\}\ge\min\{g(p\vee(q-\alpha\mathbf 1)),g((p+\alpha\mathbf 1)\wedge q)\}$ (Eq. (7.39)). (2) The strict analogue for (SSQSBw) when $g(p)\ne g(q)$. (3) For $g$ satisfying (SSQSB), the implication pair (7.41)-(7.42).
--
--   **Formalization Note.** The book's own "In particular" specializations (Eqs. (7.40), (7.43), (7.44)), restricting $\alpha$ to a sorted-gap range $[0,\alpha_1-\alpha_2]$ tied to a specific coordinate set $X=\arg\max_v\{q(v)-p(v)\}$, are not restated as separate clauses: they are named corollaries of the general statement already given (valid for every $\alpha\in\mathbb Z$ and every $p,q$), not independent content — see `MODERATION_NOTES.md`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.200, Proposition 7.50.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.200, Proposition 7.50

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SSQSB
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_QSBw
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SSQSBw

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 7.50 (p.200). Translation-perturbation inequalities for (QSBw)-, (SSQSBw)-, and
(SSQSB)-functions invariant under the all-ones shift. -/
theorem quasi_submodular_translation_inequalities (g : (V → ℤ) → WithTop ℝ)
    (hper : ∀ p : V → ℤ, g (p + 1) = g p) :
    (QSBw g → ∀ p q : V → ℤ, ∀ alpha : ℤ,
        max (g p) (g q) ≥
          min (g (fun v => max (p v) (q v - alpha))) (g (fun v => min (p v + alpha) (q v)))) ∧
    (SSQSBw g → ∀ p q : V → ℤ, g p ≠ g q → ∀ alpha : ℤ,
        max (g p) (g q) >
          min (g (fun v => max (p v) (q v - alpha))) (g (fun v => min (p v + alpha) (q v)))) ∧
    (SSQSB g → ∀ p q : V → ℤ, ∀ alpha : ℤ,
        (g (fun v => max (p v) (q v - alpha)) ≥ g p →
          g (fun v => min (p v + alpha) (q v)) ≤ g q) ∧
        (g (fun v => min (p v + alpha) (q v)) ≥ g q →
          g (fun v => max (p v) (q v - alpha)) ≤ g p)) := by sorry

end DiscreteConvex.LConvexFunctionsD
