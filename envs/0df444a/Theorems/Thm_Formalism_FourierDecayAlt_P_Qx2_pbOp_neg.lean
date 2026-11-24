-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_pbOp_neg
-- name    : Formalism.FourierDecayAlt.P.Qx2.pbOp_neg
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:20:42.382835+00:00
-- url     : https://prove2.me/theorems/f6b42d0a-861c-4c20-b06b-11ddbf2efc69
-- title:
--   Qx2: pb Op neg
-- statement:
--   The Qx2 construction uses the pb Op neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean#L23-L27

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

theorem Formalism.FourierDecayAlt.P.Qx2.pbOp_neg (l : Fin m) (f : (Fin m → ℂ) → E) : pbOp l (-f) = -pbOp l f := by sorry
