-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_horiz_bound
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_horiz_bound
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:17:16.427865+00:00
-- url     : https://prove2.me/theorems/d39f6527-b5fa-46fa-bed2-3ebec3295bae
-- title:
--   Primes In Progressions: ex horiz bound
-- statement:
--   The Primes In Progressions construction uses the ex horiz bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplEdge.lean#L46-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplEdge.lean#L46-L73

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_horiz_bound {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (y σ₁ σ₀ v B : ℝ) (hy : 1 ≤ y)
    (hσ : σ₁ ≤ σ₀) (hv : 1 ≤ |v|) (hB0 : 0 ≤ B)
    (hB : ∀ x : ℝ, σ₁ ≤ x → x ≤ σ₀ → ‖negLD χ ((x : ℂ) + v * I)‖ ≤ B) :
    ‖∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + v * I)‖ ≤ (σ₀ - σ₁) * B * y ^ σ₀ / v ^ 2 := by sorry
