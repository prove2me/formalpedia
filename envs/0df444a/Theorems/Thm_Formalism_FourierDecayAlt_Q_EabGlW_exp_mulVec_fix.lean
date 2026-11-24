-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_exp_mulVec_fix
-- name    : Formalism.FourierDecayAlt.Q.EabGlW.exp_mulVec_fix
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:44:16.078891+00:00
-- url     : https://prove2.me/theorems/5c843a72-0ba5-4165-ac67-d6476df61ff7
-- title:
--   Eab Gl W: exp mul Vec fix
-- statement:
--   The Eab Gl W construction uses the exp mul Vec fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/ExpMulVecFix.lean#L17-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/ExpMulVecFix.lean#L17-L31

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
set_option backward.isDefEq.respectTransparency false
open scoped Norms.Operator

theorem Formalism.FourierDecayAlt.Q.EabGlW.exp_mulVec_fix {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (h : Y *ᵥ v = 0) :
    NormedSpace.exp Y *ᵥ v = v := by sorry
