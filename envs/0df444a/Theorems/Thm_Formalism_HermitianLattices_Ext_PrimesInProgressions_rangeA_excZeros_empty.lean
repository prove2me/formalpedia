-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_rangeA_excZeros_empty
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.rangeA_excZeros_empty
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:17:51.019877+00:00
-- url     : https://prove2.me/theorems/c605a98a-413e-5713-9f2f-5f4fa20ee5e9
-- title:
--   Primes In Progressions: range A exc Zeros empty
-- statement:
--   The Primes In Progressions construction uses the range A exc Zeros empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTRangeA.lean#L70-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTRangeA.lean#L70-L75

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTRangeA
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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.rangeA_excZeros_empty (M : ℕ) [NeZero M] (hM : 2 ≤ M) (χ : DirichletCharacter ℂ M)
    (h : ∀ β : ℝ, eOf M = some (χ, β) → ¬ InRegion cZ M (β : ℂ)) : ExcZeros cZ χ ∅ := by sorry
