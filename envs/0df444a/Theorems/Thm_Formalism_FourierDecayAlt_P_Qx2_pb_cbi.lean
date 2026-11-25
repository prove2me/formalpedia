-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_pb_cbi
-- name    : Formalism.FourierDecayAlt.P.Qx2.pb_cbi
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:22:14.574948+00:00
-- url     : https://prove2.me/theorems/49da4b5f-c7eb-4205-87e3-41fe58602377
-- title:
--   Qx2: pb cbi
-- statement:
--   The Qx2 construction uses the pb cbi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L37-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L37-L46

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
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ}

theorem Formalism.FourierDecayAlt.P.Qx2.pb_cbi (l : Fin m) {f : (Fin m → ℂ) → E} (hf : f ∈ WSm m E) :
    pbOp l (cbiOp l f) = cbiOp l (pbOp l f) - cbiOp l f := by sorry
