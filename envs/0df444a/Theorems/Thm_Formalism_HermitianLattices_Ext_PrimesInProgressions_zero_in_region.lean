-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_zero_in_region
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.zero_in_region
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:32:06.087991+00:00
-- url     : https://prove2.me/theorems/bca7a066-809f-53a6-bb30-8255856abd4a
-- title:
--   Primes In Progressions: zero in region
-- statement:
--   The Primes In Progressions construction uses the zero in region property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTEOf.lean#L102-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTEOf.lean#L102-L116

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DeuringHeilbronnM
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.zero_in_region (M : ℕ) [NeZero M] (hM : 2 ≤ M) (χ : DirichletCharacter ℂ M) (s : ℂ)
    (hs : InRegion cZ M s) (hz : IsLZero χ s) :
    ∃ β₁ : ℝ, eOf M = some (χ, β₁) ∧ s = (β₁ : ℂ) ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 := by sorry
