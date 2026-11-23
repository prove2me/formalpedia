-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_liftRel_symm
-- name    : Formalism.FourierDecayAlt.P.A5x2.liftRel_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:41.034217+00:00
-- url     : https://prove2.me/theorems/8592bffc-3616-45ca-94f9-0b6268c2cadc
-- title:
--   A5x2: lift Rel symm
-- statement:
--   The A5x2 construction uses the lift Rel symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L239-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L239-L241

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

theorem Formalism.FourierDecayAlt.P.A5x2.liftRel_symm {k : ℕ} {Z Z' : Matrix (Fin n) (Fin n) K} {φ : coker R Z ≃ₗ[R] coker R Z'}
    {v v' : Fin n → R} (h : LiftRel R k Z Z' φ v v') : LiftRel R k Z' Z φ.symm v' v := by sorry
