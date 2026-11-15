-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_compact_preleft_C2_uniform_mesh_epsilon_energy_control
-- name    : AvramDividend.Classical.avram_b24_original_compact_preleft_C2_uniform_mesh_epsilon_energy_control
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:11:36.748949+00:00
-- url     : https://prove2.me/theorems/ed7d66ab-25b7-4746-9c93-e5f5b170b220
-- title:
--   Original compact pre-left C2 physical Ito mesh remainder has eventual epsilon times energy expectation
-- statement:
--   For the original Levy source, actual left-limit post-payment reserve and centred original source increments, if all active cells stay in a compact C2 interior interval and the maximal cell increment vanishes in probability-a.s. uniformly, then the expected absolute Taylor residual is eventually at most epsilon times the expected quadratic mesh energy. This is the original-mesh application of the Proved compact Taylor L1 estimate.
-- source:
--   Proved avram_b24_original_preleft_C2_compact_taylor_L1_automatic, exact physical source and interior compact localisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_compact_preleft_C2_uniform_mesh_epsilon_energy_control
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C)
    (A : Set Ω) (S : ℕ → Finset ℕ) (s t : ℕ → ℕ → ℝ≥0) :
    let z : ℕ → Ω → ℕ → ℝ := fun k ω i =>
      Function.leftLim (fun u : ℝ≥0 =>
        x + X.X u ω - rightLimit D u ω) (s k i)
    let g : ℕ → Ω → ℕ → ℝ := fun k ω i =>
      X.X (t k i) ω - X.X (s k i) ω -
        ((t k i - s k i : ℝ≥0) : ℝ) * X.c
    let R : ℕ → Ω → ℝ := fun k ω => ∑ i ∈ S k,
      (w (z k ω i + g k ω i) -
        taylorWithinEval w 1
          (Set.uIcc (z k ω i) (z k ω i + g k ω i))
          (z k ω i) (z k ω i + g k ω i) -
        (iteratedDeriv 2 w (z k ω i) * (g k ω i)^2) / 2)
    let Q : ℕ → Ω → ℝ := fun k ω =>
      ∑ i ∈ S k, (g k ω i)^2
    (∀ k, ∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S k,
      z k ω i ∈ Icc a b ∧ z k ω i + g k ω i ∈ Icc a b ∧
        z k ω i ≠ z k ω i + g k ω i) →
    (∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ k, K ≤ k →
      ∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S k,
        dist (z k ω i + g k ω i) (z k ω i) < δ) →
    (∀ k, AEStronglyMeasurable (Q k) (P.restrict A)) →
    (∀ k, AEStronglyMeasurable (fun ω => |R k ω|) (P.restrict A)) →
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k, K ≤ k →
      (∫ ω in A, |R k ω| ∂P) ≤
        ε * (∫ ω in A, Q k ω ∂P) := by sorry
