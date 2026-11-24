-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_loc_smooth
-- name    : Formalism.FourierDecayAlt.Q.EabGlW.loc_smooth
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:23:35.68218+00:00
-- url     : https://prove2.me/theorems/56695be9-dda1-4544-9ca8-296901b033a2
-- title:
--   Eab Gl W: loc smooth
-- statement:
--   The Eab Gl W construction uses the loc smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/ExpMulVecFix.lean#L67-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/ExpMulVecFix.lean#L67-L70

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ExpMulVecFix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabGlW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.Q.EabGlW.loc_smooth {F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (Z : Matrix (Fin n) (Fin n) ℂ) :
    ContDiffOn ℝ ∞ (fun k => fderiv ℝ F k (k * Z)) U := by sorry
