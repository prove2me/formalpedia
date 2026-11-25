-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_left_bound
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_left_bound
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:17:04.064877+00:00
-- url     : https://prove2.me/theorems/17a0a406-906e-4cac-98f7-8e66f163b6a0
-- title:
--   Primes In Progressions: ex left bound
-- statement:
--   The Primes In Progressions construction uses the ex left bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplEdge.lean#L12-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplEdge.lean#L12-L44

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_left_bound {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (y σ₁ T' B : ℝ) (hy : 1 ≤ y)
    (hσ : 1 / 2 ≤ σ₁) (hσ1 : σ₁ < 1) (hT' : 0 ≤ T')
    (hB : ∀ t : ℝ, |t| ≤ T' → ‖negLD χ ((σ₁ : ℂ) + t * I)‖ ≤ B) :
    ‖∫ t in (-T')..T', Fchi χ y ((σ₁ : ℂ) + t * I)‖ ≤ 2 * T' * B * y ^ σ₁ / (σ₁ * (1 - σ₁)) := by sorry
