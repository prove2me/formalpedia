-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_MS_le_ker
-- name    : Formalism.FourierDecayAlt.P.ClosureOperators.MS_le_ker
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:49:42.57511+00:00
-- url     : https://prove2.me/theorems/f113ef32-6e31-4865-87a0-60761dfd2fd4
-- title:
--   Closure Operators: MS le ker
-- statement:
--   The Closure Operators construction uses the MS le ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ClosureOperators.lean#L125-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ClosureOperators.lean#L125-L130

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

theorem Formalism.FourierDecayAlt.P.ClosureOperators.MS_le_ker {n : ℕ} (f : Fin n → Module.End ℂ V) (v : V) (ξ : Module.Dual ℂ V)
    (h : ∀ a : Fin n → ℕ, ξ (mono f a v) = 0) : MS f v ≤ LinearMap.ker ξ := by sorry
