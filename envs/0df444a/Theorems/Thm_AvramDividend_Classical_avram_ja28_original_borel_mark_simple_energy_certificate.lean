-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja28_original_borel_mark_simple_energy_certificate
-- name    : AvramDividend.Classical.avram_ja28_original_borel_mark_simple_energy_certificate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:35:54.122234+00:00
-- url     : https://prove2.me/theorems/67336b2d-222d-4aed-a5f9-a0193235459e
-- title:
--   Original finite-strip marked Poisson L2 certificate via genuine disjoint Borel mark cells
-- statement:
--   Construct finite deterministic Borel mark partitions B(k,i) of the exact cutoff strip, with physical original-jump counts, weighted-centred sums F_k, exact original count-covariance energy E_k, a common original-space integrable square envelope, convergence of squares to the genuine marked sum, and convergence of the deterministic energies. The requirement is on the original path X and cannot be met by unrelated Poisson or Brownian models without a proved same-space identification.
-- source:
--   Necessary physical construction for ec5fe7b6 through Proved 609c7dc5; existing harmonic annulus isometries do not yield arbitrary Borel mark-cell covariances within a fixed strip.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_ja28_original_borel_mark_simple_energy_certificate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n m : ℕ), n ≤ m → ∀ (t : ℝ≥0),
      let S : Set ℝ :=
        Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      let C : Ω → ℝ := fun ω =>
        (∫ p in (Ioc 0 t ×ˢ S), p.2 ∂NX ω) -
          (t : ℝ) * (∫ z in S, z ∂X.ν)
      let e : ℝ := (t : ℝ) * (∫ z in S, z ^ 2 ∂X.ν)
      ∃ (K : ℕ → ℕ) (B : ℕ → ℕ → Set ℝ)
        (c : ℕ → ℕ → ℝ) (g : Ω → ℝ),
        let F : ℕ → Ω → ℝ := fun k ω =>
          ∑ i ∈ Finset.range (K k),
            c k i * ((NX ω (Ioc 0 t ×ˢ B k i)).toReal -
              (((t : ℝ≥0∞) * X.ν (B k i)).toReal))
        let E : ℕ → ℝ := fun k =>
          ∑ i ∈ Finset.range (K k),
            (c k i) ^ 2 * (((t : ℝ≥0∞) * X.ν (B k i)).toReal)
        (∀ k, ∀ i ∈ Finset.range (K k),
          MeasurableSet (B k i) ∧ B k i ⊆ S) ∧
        (∀ k, ∀ i ∈ Finset.range (K k), ∀ j ∈ Finset.range (K k),
          i ≠ j → Disjoint (B k i) (B k j)) ∧
        (∀ k, AEStronglyMeasurable (fun ω => (F k ω) ^ 2) P) ∧
        Integrable g P ∧
        (∀ k, ∀ᵐ ω ∂P, ‖(F k ω) ^ 2‖ ≤ g ω) ∧
        (∀ᵐ ω ∂P,
          Tendsto (fun k => (F k ω) ^ 2) atTop (𝓝 ((C ω) ^ 2))) ∧
        (∀ k, (∫ ω, (F k ω) ^ 2 ∂P) = E k) ∧
        Tendsto E atTop (𝓝 e) := by sorry
