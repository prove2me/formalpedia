-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_siegel_bound_key_rearrange
-- name    : Formalism.ZeroFreeDirichlet.siegel_bound_key_rearrange
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:52:25.916699+00:00
-- url     : https://prove2.me/theorems/b796f2bf-9858-5b1f-b1fb-9ad849aea8f6
-- title:
--   Zero Free Dirichlet: siegel bound key rearrange
-- statement:
--   The Zero Free Dirichlet construction uses the siegel bound key rearrange property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelBoundSameCharacter.lean#L17-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SiegelBoundSameCharacter.lean#L17-L62

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

theorem Formalism.ZeroFreeDirichlet.siegel_bound_key_rearrange {C A₁ CL x ℓ a K ε q₁ q : ℝ} (hε : 0 < ε) (ha : 0 < a)
    (hKa : K * a ≤ ε / 2) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) (hA₁ : 0 ≤ A₁) (hx : 0 ≤ x) (hℓ0 : 0 ≤ ℓ)
    (hℓ : ℓ ≤ CL * Real.log (3 * (q₁ * q)))
    (hkey : 1 / 2 - C * (A₁ * x * ℓ) * (q₁ * q) ^ (K * a) / a ≤ 0) :
    a / (2 * (max C 1 * max A₁ 1 * max CL 1 * (2 * (3 : ℝ) ^ (ε / 2) / ε)) * q₁ ^ ε) * q ^ (-ε) ≤ x := by sorry
