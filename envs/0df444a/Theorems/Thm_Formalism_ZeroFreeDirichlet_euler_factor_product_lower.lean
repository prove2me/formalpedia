-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_euler_factor_product_lower
-- name    : Formalism.ZeroFreeDirichlet.euler_factor_product_lower
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:43:38.319617+00:00
-- url     : https://prove2.me/theorems/ad008a7f-1ee9-4451-a7ce-2fb22109b8d5
-- title:
--   Zero Free Dirichlet: euler factor product lower
-- statement:
--   The Zero Free Dirichlet construction uses the euler factor product lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SameCharacterLFunctionOne.lean#L74-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SameCharacterLFunctionOne.lean#L74-L85

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SameCharacterLFunctionOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.euler_factor_product_lower {M : ℕ} (φ : DirichletCharacter ℂ M) (S : Finset ℕ)
    (hS : ∀ p ∈ S, 2 ≤ p) :
    ∏ p ∈ S, (1 - 1 / (p : ℝ)) ≤ ‖∏ p ∈ S, (1 - φ (p : ZMod M) * (p : ℂ) ^ (-(1 : ℂ)))‖ := by sorry
