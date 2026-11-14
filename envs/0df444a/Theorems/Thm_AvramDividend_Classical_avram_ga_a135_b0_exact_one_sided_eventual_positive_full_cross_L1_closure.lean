-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a135_b0_exact_one_sided_eventual_positive_full_cross_L1_closure
-- name    : AvramDividend.Classical.avram_ga_a135_b0_exact_one_sided_eventual_positive_full_cross_L1_closure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:31:54.109203+00:00
-- url     : https://prove2.me/theorems/7d3eb104-4e34-46d0-afa5-00b4618e0272
-- title:
--   Original b0 source exact masked expected positive L1 closes from eventual integrability and positive-only full/cross physical source errors
-- statement:
--   The actual stopped Gaussian positive-interior spatial root expected positive error converges to zero if its positive part is eventually integrable and if the positive parts of the genuinely full pre-stop and the uniquely clipped stopping-cell source errors are integrable with expectations converging to zero. The exact identity is certified by ga123 and the eventual positive-only squeeze is ga133, removing both the all-m integrability and the full-cell absolute-L1 requirements.
-- source:
--   Certified original b0 actual physical full/cross partition ga123, positive-only eventual expected-L1 squeeze ga133, and original source analytical positive full ga134 and crossing ga120.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a123_b0_original_root_exact_genuine_full_cross_residual_identity
import Theorems.Thm_AvramDividend_Classical_avram_ga_a133_original_masked_positive_full_cross_expected_L1_eventual_integrability
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a135_b0_exact_one_sided_eventual_positive_full_cross_L1_closure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (q : ℝ) (n : ℕ) (ρ : Ω → ℝ≥0) :
    let U : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      (∑ i ∈ Finset.range m,
        E (v (i + 1)) * (w (Z i) - w (Y (v i)))) -
      (∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then
          let y := Y s
          let z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
          E s * (deriv w y * z +
            (iteratedDeriv 2 w y / 2) * (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
        else 0) -
      (∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then (Δ : ℝ) * E s * X.generator w (Y s) else 0)
    let Full : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i => E (s i) * (deriv w (Y (s i)) * Z i +
      (iteratedDeriv 2 w (Y (s i)) / 2) * (Z i^2 - (Δ : ℝ) * X.σ^2)) +
      (Δ : ℝ) * E (s i) * X.generator w (Y (s i))
    let F : ℕ → ℝ := fun i => E (s i + Δ) * (w (Y (s i) + R i) - w (Y (s i))) - H i
    ∑ i ∈ Finset.range m,
      if s i < ρ ω ∧ s i + Δ ≤ ρ ω then F i else 0
    let Cross : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i => E (s i) * (deriv w (Y (s i)) * Z i +
      (iteratedDeriv 2 w (Y (s i)) / 2) * (Z i^2 - (Δ : ℝ) * X.σ^2)) +
      (Δ : ℝ) * E (s i) * X.generator w (Y (s i))
    let Ccell : ℕ → ℝ := fun i => E (ρ ω) * (w (Y (s i) +
      (X.X (ρ ω) ω - X.X (s i) ω)) - w (Y (s i))) - H i
    ∑ i ∈ Finset.range m,
      if s i < ρ ω ∧ ρ ω < s i + Δ then Ccell i else 0

    (∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => if 0 < ρ ω then max (U m ω) 0 else 0) P) →
    (∀ m, Integrable (fun ω => max (Full m ω) 0) P) →
    (∀ m, Integrable (fun ω => max (Cross m ω) 0) P) →
    Tendsto (fun m => ∫ ω, max (Full m ω) 0 ∂P) atTop (nhds (0 : ℝ)) →
    Tendsto (fun m => ∫ ω, max (Cross m ω) 0 ∂P) atTop (nhds (0 : ℝ)) →
    Tendsto (fun m => ∫ ω,
      (if 0 < ρ ω then max (U m ω) 0 else 0) ∂P) atTop (nhds (0 : ℝ)) := by sorry
