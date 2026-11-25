-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_tail_bound
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_tail_bound
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:18:13.0677+00:00
-- url     : https://prove2.me/theorems/6c4e61e3-a3d6-4c5e-8a4e-75edbea5c32a
-- title:
--   Primes In Progressions: ex tail bound
-- statement:
--   The Primes In Progressions construction uses the ex tail bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplEdge.lean#L113-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplEdge.lean#L113-L148

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplDefs
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplEdge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_tail_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (y σ₀ T' : ℝ),
    1 ≤ y → 1 < σ₀ → 1 ≤ T' →
    ‖(∫ t : ℝ, Fchi χ y ((σ₀ : ℂ) + t * I)) - ∫ t in (-T')..T', Fchi χ y ((σ₀ : ℂ) + t * I)‖ ≤
      2 * (1 / (σ₀ - 1) + C) * y ^ σ₀ / T' := by sorry
