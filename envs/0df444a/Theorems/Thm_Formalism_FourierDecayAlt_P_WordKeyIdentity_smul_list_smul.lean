-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WordKeyIdentity_smul_list_smul
-- name    : Formalism.FourierDecayAlt.P.WordKeyIdentity.smul_list_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:53:21.172417+00:00
-- url     : https://prove2.me/theorems/5be5230e-63ff-4693-bf17-ab39134e3157
-- title:
--   Word Key Identity: smul list smul
-- statement:
--   The Word Key Identity construction uses the smul list smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordKeyIdentity.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordKeyIdentity.lean#L34-L38

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordKeyIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordKeyIdentity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.WordKeyIdentity.smul_list_smul {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℂ) (l : List ι) (a : ι → ℂ)
    (x : ι → E) : c • (l.map fun i => a i • x i).sum = (l.map fun i => a i • (c • x i)).sum := by sorry
