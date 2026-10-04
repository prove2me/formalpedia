-- Prove2me | Theorems.Thm_DiscreteConvex_CombinatorialC_prop_2_25_series_circuit_merge
-- name    : DiscreteConvex.CombinatorialC.prop_2_25_series_circuit_merge
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T21:46:12.605688+00:00
-- url     : https://prove2.me/theorems/880cc83c-1360-4ece-bd26-2f6c6b87a625
-- title:
--   Proposition 2.25 -- merging two circuits along a series arc set
-- statement:
--   If two circuits' positive supports meet in $S$, a merged circuit exists with the stated support inclusions.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.84, Proposition 2.25.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.84, Proposition 2.25

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_IsCircuit
import Definitions.Def_DiscreteConvex_CombinatorialC_IsSeriesArcSet
import Definitions.Def_DiscreteConvex_CombinatorialC_SuppPosR
import Definitions.Def_DiscreteConvex_CombinatorialC_SuppNegR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.84, Proposition 2.25, in
`DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- **Proposition 2.25.** Let `S` be a series arc set and `π1, π2` be circuits. If
`supp⁺(π1) ∩ supp⁺(π2) ∩ S ≠ ∅`, there exists a circuit `π` such that
`supp⁺(π) ⊆ supp⁺(π1) ∪ supp⁺(π2)`, `supp⁻(π) ⊆ supp⁻(π1) ∪ supp⁻(π2)`, and
`supp⁺(π) ∩ S = (supp⁺(π1) ∪ supp⁺(π2)) ∩ S`. -/
theorem prop_2_25_series_circuit_merge {V A : Type*} [Fintype A] [Fintype V] [DecidableEq V]
    [DecidableEq A] (src dst : A → V) (S : Finset A) (hS : IsSeriesArcSet src dst S)
    (pi1 pi2 : A → ℝ) (hpi1 : IsCircuit src dst pi1) (hpi2 : IsCircuit src dst pi2)
    (hne : (SuppPosR pi1 ∩ SuppPosR pi2 ∩ S).Nonempty) :
    ∃ pi : A → ℝ, IsCircuit src dst pi ∧ SuppPosR pi ⊆ SuppPosR pi1 ∪ SuppPosR pi2 ∧
      SuppNegR pi ⊆ SuppNegR pi1 ∪ SuppNegR pi2 ∧
      SuppPosR pi ∩ S = (SuppPosR pi1 ∪ SuppPosR pi2) ∩ S := by sorry

end DiscreteConvex.CombinatorialC
