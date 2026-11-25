-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_mainPsi_sum_some
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.mainPsi_sum_some
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:18:07.972185+00:00
-- url     : https://prove2.me/theorems/da8c515b-2074-4fc3-8612-9f117b6a82b0
-- title:
--   Primes In Progressions: main Psi sum some
-- statement:
--   The Primes In Progressions construction uses the main Psi sum some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiA.lean#L145-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiA.lean#L145-L167

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiB
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelWalfiszAPOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_ExcTerm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiA
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
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet ArithmeticFunction

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.mainPsi_sum_some (M : ℕ) [NeZero M] (b : ℕ) (hb : b.Coprime M) (χ₁ : DirichletCharacter ℂ M)
    (β t : ℝ) (ht : 0 ≤ t) (hχ : χ₁ (b : ZMod M) = 1 ∨ χ₁ (b : ZMod M) = -1) :
    ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * mainPsi (some (χ₁, β)) χ t =
      ((t - (χ₁ (b : ZMod M)).re * t ^ β / β : ℝ) : ℂ) := by sorry
