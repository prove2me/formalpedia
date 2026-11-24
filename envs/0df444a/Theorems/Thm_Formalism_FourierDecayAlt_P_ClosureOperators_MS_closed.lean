-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_MS_closed
-- name    : Formalism.FourierDecayAlt.P.ClosureOperators.MS_closed
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:48:54.166271+00:00
-- url     : https://prove2.me/theorems/7f73a83b-35ba-4969-b985-cbbcce23955e
-- title:
--   Closure Operators: MS closed
-- statement:
--   The Closure Operators construction uses the MS closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ClosureOperators.lean#L112-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ClosureOperators.lean#L112-L123

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

theorem Formalism.FourierDecayAlt.P.ClosureOperators.MS_closed {n : ℕ} (f : Fin n → Module.End ℂ V) (hf : ∀ a b, f a * f b = f b * f a) (v : V) (x : Fin n) :
    ∀ p ∈ MS f v, f x p ∈ MS f v := by sorry
