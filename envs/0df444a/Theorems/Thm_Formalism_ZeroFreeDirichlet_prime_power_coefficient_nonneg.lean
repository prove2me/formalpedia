-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_prime_power_coefficient_nonneg
-- name    : Formalism.ZeroFreeDirichlet.prime_power_coefficient_nonneg
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:44:08.960728+00:00
-- url     : https://prove2.me/theorems/8f3e6cc4-127f-4a11-b036-f21a5726dedf
-- title:
--   Zero Free Dirichlet: prime power coefficient nonneg
-- statement:
--   The Zero Free Dirichlet construction uses the prime power coefficient nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ConvolutionNonnegOfDivisors.lean#L41-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ConvolutionNonnegOfDivisors.lean#L41-L70

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
set_option backward.isDefEq.respectTransparency.types false

theorem Formalism.ZeroFreeDirichlet.prime_power_coefficient_nonneg {N N' M : ℕ} {χ : DirichletCharacter ℂ N} {χ' : DirichletCharacter ℂ N'}
    {ψ : DirichletCharacter ℂ M} (hχ : χ ^ 2 = 1) (hψ : ∀ n : ℕ, ψ (n : ZMod M) = χ (n : ZMod N) * χ' (n : ZMod N'))
    {p : ℕ} (hp : p.Prime)
    (hc : χ' (p : ZMod N') = 0 ∨ χ' (p : ZMod N') = 1 ∨ (χ' (p : ZMod N') = -1 ∧ χ (p : ZMod N) = -1))
    (k : ℕ) :
    0 ≤ (DirichletCharacter.zetaMul χ * (toArithmeticFunction (fun m : ℕ => χ' (m : ZMod N')) *
      toArithmeticFunction (fun m : ℕ => ψ (m : ZMod M)))) (p ^ k) := by sorry
