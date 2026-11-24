-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_herm_bvec_out
-- name    : Formalism.FourierDecayAlt.P.Qx2.herm_bvec_out
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:20:14.637348+00:00
-- url     : https://prove2.me/theorems/6bb69215-da4a-4ebd-96ed-d4b6bf5e90ef
-- title:
--   Qx2: herm bvec out
-- statement:
--   The Qx2 construction uses the herm bvec out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L814-L821
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L814-L821

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {i : Fin (r + 1)}

theorem Formalism.FourierDecayAlt.P.Qx2.herm_bvec_out {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {p : Fin (2 * r + k + 1)}
    (hp : ¬ inV k r i p) : herm (Hpk k r) (bvec p) (fvec k r z i) = 0 := by sorry
