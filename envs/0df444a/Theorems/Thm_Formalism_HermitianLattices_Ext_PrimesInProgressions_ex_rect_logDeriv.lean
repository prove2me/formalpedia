-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_rect_logDeriv
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_rect_logDeriv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:17:52.336655+00:00
-- url     : https://prove2.me/theorems/31b2f82e-10ed-4f89-b7c2-20fee33ffe0a
-- title:
--   Primes In Progressions: ex rect log Deriv
-- statement:
--   The Primes In Progressions construction uses the ex rect log Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplRect.lean#L18-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplRect.lean#L18-L189

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRectA
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZeroFactor
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_RectResidue
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRect
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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_rect_logDeriv (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf1 : f 1 ≠ 0) (y : ℝ) (hy : 0 < y)
    (x₀ x₁ y₀ y₁ : ℝ) (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) (hx₁ : 1 < x₁) (hy₀ : y₀ < 0) (hy₁ : 0 < y₁)
    (Z : Finset ℂ) (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (f ρ = 0 ∧ x₀ < ρ.re ∧ ρ.re < x₁ ∧ y₀ < ρ.im ∧ ρ.im < y₁))
    (hedge : ∀ w : ℂ, x₀ ≤ w.re → w.re ≤ x₁ → y₀ ≤ w.im → w.im ≤ y₁ → f w = 0 →
      x₀ < w.re ∧ w.re < x₁ ∧ y₀ < w.im ∧ w.im < y₁) :
    Formalism.ZF.rectInt (fun w => -(deriv f w / f w) * exKer y w) x₀ x₁ y₀ y₁ =
      2 * Real.pi * I * (-(deriv f 1 / f 1) * y - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * exKer y ρ) := by sorry
