-- Prove2me | Theorems.Thm_Formalism_HadamardInequality_P_tr_dual
-- name    : Formalism.HadamardInequality.P.tr_dual
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:10:44.683681+00:00
-- url     : https://prove2.me/theorems/c298e3d0-1b44-4b79-b43b-73012f414513
-- title:
--   P: tr dual
-- statement:
--   The P construction uses the tr dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GelfandTransference/HadamardGelfand/Transference.lean#L184-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GelfandTransference/HadamardGelfand/Transference.lean#L184-L240

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

theorem Formalism.HadamardInequality.P.tr_dual {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Submodule ℤ E) (hspan : span ℝ (M : Set E) = ⊤)
    (W : Submodule ℝ E) {t : ℝ} (ht : 0 < t)
    (hmin : ∀ m ∈ M, Wᗮ.starProjection m ≠ 0 → t ≤ ‖Wᗮ.starProjection m‖) :
    ∃ y : Fin (finrank ℝ Wᗮ) → E, (∀ j, y j ∈ Formalism.HadamardInequality.zdual M) ∧ LinearIndependent ℝ y ∧
      ∀ j, ‖y j‖ ≤ (finrank ℝ Wᗮ : ℝ) ^ ((3 : ℝ) / 2) / t := by sorry
