-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_rect_Fchi
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_rect_Fchi
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:35:29.057817+00:00
-- url     : https://prove2.me/theorems/164d7b8f-d9e4-5c2e-a5e2-3534d219994a
-- title:
--   Primes In Progressions: ex rect Fchi
-- statement:
--   The Primes In Progressions construction uses the ex rect Fchi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplRectF.lean#L154-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplRectF.lean#L154-L240

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRect
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRectF
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
set_option maxHeartbeats 800000

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_rect_Fchi {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (y : ℝ) (hy : 0 < y) (σ₁ σ₀ T' : ℝ)
    (hσ₁ : 0 < σ₁) (hσ₁1 : σ₁ < 1) (hσ₀ : 1 < σ₀) (hT' : 0 < T')
    (Z : Finset ℂ) (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (exLF χ ρ = 0 ∧ σ₁ < ρ.re ∧ |ρ.im| < T'))
    (hedge : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₀ → |w.im| ≤ T' → exLF χ w = 0 → σ₁ < w.re ∧ |w.im| < T') :
    Formalism.ZF.rectInt (Fchi χ y) σ₁ σ₀ (-T') T' =
      2 * Real.pi * I * (explicitFormulaConstant χ * y + (if χ = 1 then (y : ℂ) * (Real.log y : ℂ) - y else 0) -
        ∑ ρ ∈ Z, (exOrd χ ρ : ℂ) * exKer y ρ) := by sorry
