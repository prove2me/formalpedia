-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lift_lat
-- name    : Formalism.FourierDecayAlt.P.A5x2.lift_lat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:02:16.81865+00:00
-- url     : https://prove2.me/theorems/e4e98416-788f-4dd7-84c8-2d4fc82e8cb3
-- title:
--   A5x2: lift lat
-- statement:
--   The A5x2 construction uses the lift lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L315-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L315-L336

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
variable (R)

theorem Formalism.FourierDecayAlt.P.A5x2.lift_lat (Z Z' : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z.det) (hd' : IsUnit Z'.det)
    (φ : coker R Z ≃ₗ[R] coker R Z') (c : Fin n) (m m' v v' : Fin n → R)
    (hm : LiftRel R c.val Z Z' φ m m') (hv : LiftRel R c.val Z Z' φ v v')
    (hl : v ∈ latZ R (Z + vecMulVec (coeLin R m) (Pi.single c 1))) :
    v' ∈ latZ R (Z' + vecMulVec (coeLin R m') (Pi.single c 1)) := by sorry
