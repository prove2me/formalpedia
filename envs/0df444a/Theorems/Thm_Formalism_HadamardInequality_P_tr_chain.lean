-- Prove2me | Theorems.Thm_Formalism_HadamardInequality_P_tr_chain
-- name    : Formalism.HadamardInequality.P.tr_chain
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:10:26.498496+00:00
-- url     : https://prove2.me/theorems/abc57109-9c18-4bff-ad32-fa67b684bde2
-- title:
--   P: tr chain
-- statement:
--   The P construction uses the tr chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GelfandTransference/HadamardGelfand/Transference.lean#L67-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GelfandTransference/HadamardGelfand/Transference.lean#L67-L182

import Definitions.Def_Formalism_GelfandTransference_EnergyIdentity
import Definitions.Def_Formalism_NormUnitaryBounds_NormUnitary
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShortIndependentVectorsOfDualMinimum
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HadamardInequality Formalism.HadamardInequality.P

theorem Formalism.HadamardInequality.P.tr_chain {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Submodule ℤ E) [hMd : DiscreteTopology M]
    (hspan : span ℝ (M : Set E) = ⊤) :
    ∀ k, k ≤ finrank ℝ E → ∃ (b : Fin k → E) (t : Fin k → ℝ), (∀ i, b i ∈ M) ∧
      LinearIndependent ℝ b ∧ (∀ i, 0 < t i) ∧
      (∀ i, 4 * ‖b i‖ ^ 2 ≤ 3 * t i ^ 2 + ∑ l, t l ^ 2) ∧
      (∀ i : Fin k, ∃ W : Submodule ℝ E, finrank ℝ W = i.val ∧
          ∀ m ∈ M, Wᗮ.starProjection m ≠ 0 → t i ≤ ‖Wᗮ.starProjection m‖) ∧
      (∀ w ∈ span ℝ (Set.range b), ∃ z ∈ span ℤ (Set.range b),
        4 * ‖w - z‖ ^ 2 ≤ ∑ l, t l ^ 2) := by sorry
