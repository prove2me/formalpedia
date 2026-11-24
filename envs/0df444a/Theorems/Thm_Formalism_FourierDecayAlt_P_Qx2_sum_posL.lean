-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_sum_posL
-- name    : Formalism.FourierDecayAlt.P.Qx2.sum_posL
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:21:08.303123+00:00
-- url     : https://prove2.me/theorems/61aa6174-456a-48bb-ac14-b367ed8cc9d8
-- title:
--   Qx2: sum pos L
-- statement:
--   The Qx2 construction uses the sum pos L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L782-L789
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L782-L789

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

theorem Formalism.FourierDecayAlt.P.Qx2.sum_posL (F : Fin (2 * r + k + 1) → ℂ) (h : ∀ p, ¬ inV k r i p → F p = 0) :
    ∑ j, F (posL k r i j) = ∑ p, F p := by sorry
