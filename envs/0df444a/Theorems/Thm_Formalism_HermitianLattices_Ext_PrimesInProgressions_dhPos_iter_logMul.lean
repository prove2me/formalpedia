-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhPos_iter_logMul
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.dhPos_iter_logMul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:13:24.266818+00:00
-- url     : https://prove2.me/theorems/bdf5bed5-519b-4670-8646-540bcee9b450
-- title:
--   Primes In Progressions: dh Pos iter log Mul
-- statement:
--   The Primes In Progressions construction uses the dh Pos iter log Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHPos.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHPos.lean#L14-L20

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHSt
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_Positivity
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPos
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
open scoped LSeries.notation

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.dhPos_iter_logMul (f : ℕ → ℂ) (k n : ℕ) :
    (logMul^[k] f) n = (Complex.log n) ^ k * f n := by sorry
