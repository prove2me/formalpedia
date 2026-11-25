-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_siegel_bound_same_character
-- name    : Formalism.ZeroFreeDirichlet.siegel_bound_same_character
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:52:56.59217+00:00
-- url     : https://prove2.me/theorems/b98f77f8-f0f0-4d4f-b573-b68871b80b6c
-- title:
--   Zero Free Dirichlet: siegel bound same character
-- statement:
--   The Zero Free Dirichlet construction uses the siegel bound same character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelBoundSameCharacter.lean#L64-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelBoundSameCharacter.lean#L64-L106

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelBoundSameCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.siegel_bound_same_character {N₀ : ℕ} (hN₀ : N₀ ≠ 0) {A₁ x ε q₁ q : ℝ} (hε : 0 < ε) (hq₁ : 1 ≤ q₁)
    (hq : 1 ≤ q) (hNq : (N₀ : ℝ) = q₁ * q) (hA₁ : 0 < A₁) (hx : 0 ≤ x)
    (hS : A₁ ≤ ((N₀.primeFactors.card : ℝ) + 1) ^ 2 * x) :
    A₁ / (4 / (ε * Real.log 2) ^ 2 * (2 : ℝ) ^ ε * q₁ ^ ε) * q ^ (-ε) ≤ x := by sorry
