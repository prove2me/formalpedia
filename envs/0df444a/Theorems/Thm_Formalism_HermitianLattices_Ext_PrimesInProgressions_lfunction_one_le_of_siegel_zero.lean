-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_lfunction_one_le_of_siegel_zero
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.lfunction_one_le_of_siegel_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:29:32.260709+00:00
-- url     : https://prove2.me/theorems/25fee2ad-c3b7-5af7-8582-71cc983b4b12
-- title:
--   Primes In Progressions: lfunction one le of siegel zero
-- statement:
--   The Primes In Progressions construction uses the lfunction one le of siegel zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHPrimeA.lean#L191-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHPrimeA.lean#L191-L208

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPos
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DHFinish2Of
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LDerivNearOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPrimeA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation ComplexOrder

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.lfunction_one_le_of_siegel_zero : ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℕ) [NeZero M] (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ),
    χ₁ ≠ 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
    1 - 1 / Real.log (3 * M) ≤ β₁ → β₁ < 1 →
    ‖DirichletCharacter.LFunction χ₁ 1‖ ≤ C * Real.log (3 * M) ^ 2 * (1 - β₁) := by sorry
