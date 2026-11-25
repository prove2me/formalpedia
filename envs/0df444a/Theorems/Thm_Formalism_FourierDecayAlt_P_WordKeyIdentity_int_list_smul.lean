-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WordKeyIdentity_int_list_smul
-- name    : Formalism.FourierDecayAlt.P.WordKeyIdentity.int_list_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:37:30.125653+00:00
-- url     : https://prove2.me/theorems/67af6798-da4b-4a35-8155-7df28581b713
-- title:
--   Word Key Identity: int list smul
-- statement:
--   The Word Key Identity construction uses the int list smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordKeyIdentity.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordKeyIdentity.lean#L29-L32

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

theorem Formalism.FourierDecayAlt.P.WordKeyIdentity.int_list_smul {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure α) (l : List ι) (a : ι → ℂ) (φ : ι → α → E) (h : ∀ i ∈ l, Integrable (φ i) μ) :
    ∫ p, (l.map fun i => a i • φ i p).sum ∂μ = (l.map fun i => a i • ∫ p, φ i p ∂μ).sum := by sorry
