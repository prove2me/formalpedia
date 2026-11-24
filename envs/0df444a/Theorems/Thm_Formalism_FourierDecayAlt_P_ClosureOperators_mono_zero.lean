-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_mono_zero
-- name    : Formalism.FourierDecayAlt.P.ClosureOperators.mono_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:51:02.065959+00:00
-- url     : https://prove2.me/theorems/3c4c59d8-dfa5-4c6a-89cd-a2d3a22f5f0d
-- title:
--   Closure Operators: mono zero
-- statement:
--   The Closure Operators construction uses the mono zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ClosureOperators.lean#L75-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ClosureOperators.lean#L75-L83

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ClosureOperators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ClosureOperators
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem Formalism.FourierDecayAlt.P.ClosureOperators.mono_zero : ∀ {n : ℕ} (f : Fin n → Module.End ℂ V), mono f (fun _ => 0) = 1 := by sorry
