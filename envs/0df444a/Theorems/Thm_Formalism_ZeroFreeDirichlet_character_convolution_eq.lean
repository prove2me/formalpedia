-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_character_convolution_eq
-- name    : Formalism.ZeroFreeDirichlet.character_convolution_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:43:22.516329+00:00
-- url     : https://prove2.me/theorems/7fa63b3b-9459-4a4e-9bc9-ce500039d8ad
-- title:
--   Zero Free Dirichlet: character convolution eq
-- statement:
--   The Zero Free Dirichlet construction uses the character convolution eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ConvolutionNonnegOfDivisors.lean#L17-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ConvolutionNonnegOfDivisors.lean#L17-L37

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

theorem Formalism.ZeroFreeDirichlet.character_convolution_eq {N N' M : ℕ} (χ : DirichletCharacter ℂ N) (χ' : DirichletCharacter ℂ N')
    (ψ : DirichletCharacter ℂ M) (hψ : ∀ n : ℕ, ψ (n : ZMod M) = χ (n : ZMod N) * χ' (n : ZMod N'))
    (n : ℕ) :
    (toArithmeticFunction (fun m : ℕ => χ' (m : ZMod N')) * toArithmeticFunction (fun m : ℕ => ψ (m : ZMod M))) n
      = χ' (n : ZMod N') * DirichletCharacter.zetaMul χ n := by sorry
