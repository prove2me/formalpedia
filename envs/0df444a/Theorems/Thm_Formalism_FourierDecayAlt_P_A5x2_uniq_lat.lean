-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_uniq_lat
-- name    : Formalism.FourierDecayAlt.P.A5x2.uniq_lat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:54.702505+00:00
-- url     : https://prove2.me/theorems/ee8058a8-f679-48f7-988b-d5cbf765e613
-- title:
--   A5x2: uniq lat
-- statement:
--   The A5x2 construction uses the uniq lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L338-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L338-L345

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

theorem Formalism.FourierDecayAlt.P.A5x2.uniq_lat (Z Z' : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z.det) (hd' : IsUnit Z'.det)
    (φ : coker R Z ≃ₗ[R] coker R Z') (c : Fin n) (m m' v v' v'' : Fin n → R)
    (hm : LiftRel R c.val Z Z' φ m m') (h1 : LiftRel R c.val Z Z' φ v v')
    (h2 : LiftRel R c.val Z Z' φ v v'') :
    v' - v'' ∈ latZ R (Z' + vecMulVec (coeLin R m') (Pi.single c 1)) := by sorry
