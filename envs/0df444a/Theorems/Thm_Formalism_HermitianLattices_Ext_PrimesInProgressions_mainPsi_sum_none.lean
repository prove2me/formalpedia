-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_mainPsi_sum_none
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.mainPsi_sum_none
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:18:40.607462+00:00
-- url     : https://prove2.me/theorems/6df3a118-906d-42be-8133-d88aaa6b786b
-- title:
--   Primes In Progressions: main Psi sum none
-- statement:
--   The Primes In Progressions construction uses the main Psi sum none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiA.lean#L135-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiA.lean#L135-L143

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.mainPsi_sum_none (M : ℕ) [NeZero M] (b : ℕ) (hb : b.Coprime M) (t β : ℝ) :
    ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * mainPsi none χ t = ((t - 0 * t ^ β / β : ℝ) : ℂ) := by sorry
