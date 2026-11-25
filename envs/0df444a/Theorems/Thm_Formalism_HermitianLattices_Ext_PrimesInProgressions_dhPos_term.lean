-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhPos_term
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.dhPos_term
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:17:21.69233+00:00
-- url     : https://prove2.me/theorems/19360681-6260-4b62-bef8-b29c36b59da8
-- title:
--   Primes In Progressions: dh Pos term
-- statement:
--   The Primes In Progressions construction uses the dh Pos term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHPos.lean#L65-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHPos.lean#L65-L82

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.dhPos_term {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (k : ℕ) (σ u : ℝ) (n : ℕ) :
    term (logMul^[k] (↗ψ * ↗Λ)) ((σ : ℂ) + u * I) n =
      (((Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) : ℝ) : ℂ) * (ψ n / (n : ℂ) ^ ((u : ℂ) * I)) := by sorry
