-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_convolution_nonneg_of_divisors
-- name    : Formalism.ZeroFreeDirichlet.convolution_nonneg_of_divisors
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:43:04.177726+00:00
-- url     : https://prove2.me/theorems/498b713b-0849-4034-b9bd-cc29d08bae5b
-- title:
--   Zero Free Dirichlet: convolution nonneg of divisors
-- statement:
--   The Zero Free Dirichlet construction uses the convolution nonneg of divisors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ConvolutionNonnegOfDivisors.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ConvolutionNonnegOfDivisors.lean#L10-L15

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ConvolutionNonnegOfDivisors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction
open scoped ComplexOrder LSeries.notation
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.convolution_nonneg_of_divisors (f g : ArithmeticFunction ℂ) (n : ℕ)
    (hf : ∀ d, d ∣ n → 0 ≤ f d) (hg : ∀ d, d ∣ n → 0 ≤ g d) : 0 ≤ (f * g) n := by sorry
