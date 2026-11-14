-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b37_original_random_stopped_C2_taylor_uniform_energy_vanish_with_zero
-- name    : AvramDividend.Classical.avram_b37_original_random_stopped_C2_taylor_uniform_energy_vanish_with_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:50:27.411204+00:00
-- url     : https://prove2.me/theorems/fab2e62c-03ca-4045-9577-05026f5e4def
-- title:
--   Original stopped physical C2 Taylor expected error vanishes with zero-increment cells
-- statement:
--   On the actual spectrally negative Lévy process, genuine finite random stopped physical meshes have vanishing expected absolute compact C2 Taylor error as their increments become fine, assuming uniformly bounded expected physical quadratic energies. Zero source increments, clipped repeated clocks, and stationary cells are permitted and contribute no Taylor error.
-- source:
--   Original B29 expected convergence and B36 source-level zero-increment-robust restricted Taylor modulus.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b36_original_random_stopped_C2_Taylor_L1_allow_zero_increments
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b37_original_random_stopped_C2_taylor_uniform_energy_vanish_with_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C) :
    ∀ (A : Set Ω) (S : ℕ → Finset ℕ)
      (s t : ℕ → ℕ → Ω → ℝ≥0),
      let z : ℕ → Ω → ℕ → ℝ := fun m ω i =>
        Function.leftLim (fun u : ℝ≥0 =>
          x + X.X u ω - rightLimit D u ω) (s m i ω)
      let g : ℕ → Ω → ℕ → ℝ := fun m ω i =>
        X.X (t m i ω) ω - X.X (s m i ω) ω -
          ((t m i ω : ℝ) - (s m i ω : ℝ)) * X.c
      let Q : ℕ → Ω → ℝ := fun m ω => ∑ i ∈ S m, (g m ω i) ^ 2
      let R : ℕ → Ω → ℝ := fun m ω => ∑ i ∈ S m,
        (w (z m ω i + g m ω i) -
          taylorWithinEval w 1
            (Set.uIcc (z m ω i) (z m ω i + g m ω i))
            (z m ω i) (z m ω i + g m ω i) -
          (iteratedDeriv 2 w (z m ω i) * (g m ω i) ^ 2) / 2)
      (∀ m i, i ∈ S m → IsStoppingTime 𝓕.rightCont
        (fun ω => (s m i ω : WithTop ℝ≥0))) →
      (∀ m i, i ∈ S m → IsStoppingTime 𝓕.rightCont
        (fun ω => (t m i ω : WithTop ℝ≥0))) →
      (∀ m, ∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S m,
        z m ω i ∈ Icc a b ∧ z m ω i + g m ω i ∈ Icc a b) →
      (∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ m, N ≤ m →
        ∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S m,
          dist (z m ω i + g m ω i) (z m ω i) < δ) →
      (∀ m, AEStronglyMeasurable (fun ω => |R m ω|) (P.restrict A)) →
      ∀ K : ℝ, 0 ≤ K →
        (∀ m, (∫ ω in A, Q m ω ∂P) ≤ K) →
        ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ m, N ≤ m →
          IntegrableOn (fun ω => |R m ω|) A P ∧
          (∫ ω in A, |R m ω| ∂P) ≤ η := by sorry
