-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_tInvariant_of_contractions
-- name    : Formalism.FourierDecayAlt.Q.TInvW.tInvariant_of_contractions
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:52:17.904378+00:00
-- url     : https://prove2.me/theorems/498ce604-31ca-49f9-8aa7-1c59fcbd9dec
-- title:
--   TInv W: t Invariant of contractions
-- statement:
--   The TInv W construction uses the t Invariant of contractions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/Development.lean#L410-L463
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/Development.lean#L410-L463

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.Q.TInvW.tInvariant_of_contractions (hCC : ContractionsCovariant) (hP : EabPres) (hG : EabGlLev) (hL : QMinorLeftH)
    (hS : StepS) (hGr : StepGrp) (hV : StepVec) (hC : StepCongr) (hRt : StepRight) (hRS : StepRSm) :
    TInvariant := by sorry
