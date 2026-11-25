-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_zeroSum_core
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.zeroSum_core
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:18:17.143548+00:00
-- url     : https://prove2.me/theorems/6ec1b292-576c-4f14-ba8f-9b6a5aae5942
-- title:
--   Primes In Progressions: zero Sum core
-- statement:
--   The Primes In Progressions construction uses the zero Sum core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTZSum.lean#L240-L572
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTZSum.lean#L240-L572

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTZSumB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTZSum
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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.zeroSum_core (a B C : ℝ) (ha : 1 ≤ a) (hB : 0 ≤ B) (hC : 1 ≤ C)
    (hdens : ∀ (M : ℕ) [NeZero M] (T v : ℝ) (S : Finset (DirichletCharacter ℂ M × ℂ)), 3 ≤ M → 2 ≤ T →
      (∀ p ∈ S, 1 / 2 ≤ p.2.re ∧ p.2.re ≤ 1 ∧ Real.log ((M : ℝ) * T) * (1 - p.2.re) ≤ v ∧ |p.2.im| ≤ T ∧
        IsLZero p.1 p.2) →
      (∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|) →
      (S.card : ℝ) ≤ C * Real.exp (a * v) * Real.log ((M : ℝ) * T) ^ B)
    (κ c2 C₁ A₁ : ℝ) (hκ : κ ≤ 1 / 20) (hc2 : 0 < c2) (hA₁ : 1 ≤ A₁)
    (M : ℕ) [NeZero M] (Z : DirichletCharacter ℂ M → Finset ℂ) (m : DirichletCharacter ℂ M → ℂ → ℕ)
    (h8 : 8 ∣ M)
    (hZ : ∀ χ, ∀ ρ ∈ Z χ, IsLZero χ ρ ∧ 1 - κ < ρ.re ∧ |ρ.im| ≤ (M : ℝ) ^ A₁ + 1)
    (hms : ∀ χ, ∀ ρ ∈ Z χ, deriv (DirichletCharacter.LFunction χ) ρ ≠ 0 → m χ ρ = 1)
    (hwin : ∀ χ, ∀ t : ℝ, ((∑ ρ ∈ (Z χ).filter (fun ρ => |ρ.im - t| ≤ 1), m χ ρ : ℕ) : ℝ) ≤
      C₁ * Real.log ((M : ℝ) * (|t| + 2)))
    (y : ℝ) (hy : 2 ≤ y)
    (hL : ((A₁ + 2) * (a + 1 + 2 / c2) + (B + 1) / (cZ / (4 * (A₁ + 2)))) * Real.log M *
      Real.log (Real.log M + 2) ≤ Real.log y)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hθ : ∀ χ, ∀ ρ ∈ Z χ, ¬ InRegion cZ M ρ →
      c2 * Real.log (1 / θ) ≤ Real.log ((M : ℝ) * ((M : ℝ) ^ A₁ + 3)) * (1 - ρ.re)) :
    ∑ χ : DirichletCharacter ℂ M, ∑ ρ ∈ Z χ, ((m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ)) * y ^ (ρ.re - 1) ≤
      (4 * |C₁| * C * Real.exp (a + a * cZ / 2) * (A₁ + 2) ^ (B + 1)) * θ *
        Real.exp (-(cZ / (4 * (A₁ + 2)) * Real.log y / Real.log M)) := by sorry
