-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_abs_psiAP_sub_le
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.abs_psiAP_sub_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:39:50.709977+00:00
-- url     : https://prove2.me/theorems/8e6856a8-7ac4-4bc9-92c3-01ff63b5d427
-- title:
--   Primes In Progressions: abs psi AP sub le
-- statement:
--   The Primes In Progressions construction uses the abs psi AP sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiA.lean#L102-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiA.lean#L102-L133

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.abs_psiAP_sub_le (M : ℕ) [NeZero M] (b : ℕ) (hb : b.Coprime M) (e : Option (DirichletCharacter ℂ M × ℝ))
    (θ β t : ℝ)
    (hmain : ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * mainPsi e χ t =
      ((t - θ * t ^ β / β : ℝ) : ℂ)) :
    |psiAP M b t - Fm (1 / (M.totient : ℝ)) θ β t| ≤
      (∑ χ : DirichletCharacter ℂ M, ‖psiChi χ t - mainPsi e χ t‖) / (M.totient : ℝ) := by sorry
