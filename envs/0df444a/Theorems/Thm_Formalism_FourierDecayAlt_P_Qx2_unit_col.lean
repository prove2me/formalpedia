-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_unit_col
-- name    : Formalism.FourierDecayAlt.P.Qx2.unit_col
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:19:27.252058+00:00
-- url     : https://prove2.me/theorems/2c059111-3a6f-4ba0-9cfa-c5df407983f1
-- title:
--   Qx2: unit col
-- statement:
--   The Qx2 construction uses the unit col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L174-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L174-L178

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
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.Qx2.unit_col {i : Fin (r + 1)} {a b p : Fin (2 * r + k + 1)} (hb : inV k r i b) (hp : ¬ inV k r i p) :
    (Matrix.single a b (1 : ℂ) : Mx k r) *ᵥ bvec p = 0 := by sorry
