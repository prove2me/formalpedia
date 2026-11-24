-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_sum_xb_y
-- name    : Formalism.FourierDecayAlt.P.Qx2.sum_xb_y
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:20:00.410709+00:00
-- url     : https://prove2.me/theorems/7462c41f-96be-4a8c-8190-68e33b8bfde2
-- title:
--   Qx2: sum xb y
-- statement:
--   The Qx2 construction uses the sum xb y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L831-L853
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L831-L853

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

theorem Formalism.FourierDecayAlt.P.Qx2.sum_xb_y (z : Fin (2 * r + k + 1) → ℂ) {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') {g : Mx k r}
    (hg : g ∈ UH (Hpk k r)) : ∑ j, xbv k r z' i j * yv k r z i g j = star (zetaL k r z z' i g) := by sorry
