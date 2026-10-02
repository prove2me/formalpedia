-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityC_m2_proximity_theorem_summands
-- name    : DiscreteConvex.ConjugacyDualityC.m2_proximity_theorem_summands
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:44:18.192715+00:00
-- url     : https://prove2.me/theorems/17bfa6b0-b8c4-4ec3-b366-afa2bc99bc53
-- title:
--   Theorem 8.34 -- m2_proximity_theorem_summands
-- statement:
--   **Theorem 8.34** (M2-proximity theorem; p.228). A scaling version of Theorem 8.33's condition guarantees $\arg\min(f_1+f_2)\ne\emptyset$ with an explicit $\|\cdot\|_\infty$ proximity bound $n^2(\alpha-1)/2$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.228, Theorem 8.34.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.228, Theorem 8.34

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IndicatorVec
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_ArgMin
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_MExchangeAxiom

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.34 (M2-proximity theorem; p.228). A scaling version of Theorem 8.33 gives an
explicit proximity bound for `arg min(f1+f2)`. -/
theorem m2_proximity_theorem_summands (f1 f2 : (V → ℤ) → WithTop ℝ) (hf1 : MExchangeAxiom f1)
    (hf2 : MExchangeAxiom f2) (alpha : ℤ) (halpha : 0 < alpha) (xalpha : V → ℤ)
    (hxalpha : xalpha ∈ DomZ f1 ∩ DomZ f2)
    (hcond : ∀ k : ℕ, ∀ u v : Fin (k + 1) → V, (∀ i j, u i ≠ v j) →
      (∑ i : Fin (k + 1),
          (f1 (fun w => xalpha w - alpha * (IndicatorVec {u i} w - IndicatorVec {v i} w)) -
            f1 xalpha)) +
        (∑ i : Fin (k + 1),
          (f2 (fun w => xalpha w + alpha * (IndicatorVec {u (i + 1)} w - IndicatorVec {v i} w)) -
            f2 xalpha)) ≥
        0) :
    (ArgMin (fun x => f1 x + f2 x)).Nonempty ∧
      ∃ xstar ∈ ArgMin (fun x => f1 x + f2 x), ∀ w : V,
        |(xalpha w : ℝ) - (xstar w : ℝ)| ≤ (((Fintype.card V : ℝ) ^ 2) / 2) * ((alpha : ℝ) - 1) := by sorry

end DiscreteConvex.ConjugacyDualityC
