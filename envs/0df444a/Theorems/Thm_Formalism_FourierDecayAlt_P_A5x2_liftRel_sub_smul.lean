-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_liftRel_sub_smul
-- name    : Formalism.FourierDecayAlt.P.A5x2.liftRel_sub_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:02:35.874167+00:00
-- url     : https://prove2.me/theorems/df9dbc29-0a9b-4be3-8c02-ca4d5db597ab
-- title:
--   A5x2: lift Rel sub smul
-- statement:
--   The A5x2 construction uses the lift Rel sub smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L232-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L232-L237

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x2
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
variable {R}

theorem Formalism.FourierDecayAlt.P.A5x2.liftRel_sub_smul {k : ℕ} {Z Z' : Matrix (Fin n) (Fin n) K} {φ : coker R Z ≃ₗ[R] coker R Z'}
    {v v' m m' : Fin n → R} (hv : LiftRel R k Z Z' φ v v') (hm : LiftRel R k Z Z' φ m m') (r : R) :
    LiftRel R k Z Z' φ (v - r • m) (v' - r • m') := by sorry
