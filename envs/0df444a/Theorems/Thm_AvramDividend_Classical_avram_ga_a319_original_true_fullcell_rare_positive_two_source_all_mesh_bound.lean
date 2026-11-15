-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a319_original_true_fullcell_rare_positive_two_source_all_mesh_bound
-- name    : AvramDividend.Classical.avram_ga_a319_original_true_fullcell_rare_positive_two_source_all_mesh_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:23:21.340977+00:00
-- url     : https://prove2.me/theorems/825cf822-f6e7-4143-9472-dc56ff7bbf62
-- title:
--   Original stopped Gaussian true fullcell rare combined positive error bounded on every mesh by exact signed and polynomial tail sources
-- statement:
--   On the actual original zerojump Gaussian stopped physical mesh with original localisation prefix, the positive part of the complete signed rare combined discounted verification error is almost surely bounded at every mesh size by a deterministic constant times the original signed Gaussian rare exponential tail plus a constant times the original raw/centered Gaussian rare polynomial tail. The constants depend only on the original HJB global envelope and compact source jet/localisation data, and are uniform over all mesh sizes and cutoff values. This directly links source a263 to proved a275 signed tail and a313 polynomial tail, without any eventual drift hypothesis.
-- source:
--   Original true Gaussian HJB a301, reserve ceiling a306 and finite source positive algebra a318.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a301_true_fullcell_discounted_positive_scalar_HJB_source_envelope
import Theorems.Thm_AvramDividend_Classical_avram_ga_a306_original_true_fullcell_preincrement_reserve_uniform_upper
import Theorems.Thm_AvramDividend_Classical_avram_ga_a318_compact_HJB_finite_combined_positive_two_stream_upper
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a319_original_true_fullcell_rare_positive_two_source_all_mesh_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let B : ℝ := x + ((j : ℝ)+1)
    let Large : ℝ → ℕ → Ω → ℝ := fun δ m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0)+1)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0)*Δ
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q*(t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω-rightLimit D t ω
      let R : ℕ → ℝ := fun i => X.X (s i+Δ) ω-X.X (s i) ω
      let Z : ℕ → ℝ := fun i => R i-(Δ : ℝ)*X.c
      ∑ i ∈ Finset.range m,
        if (s i < ρ ω ∧ s i+Δ ≤ ρ ω) ∧ δ ≤ |R i| then
          E (s i+Δ)*(w (Y (s i)+R i)-w (Y (s i))) -
          E (s i)*(deriv w (Y (s i))*R i +
              iteratedDeriv 2 w (Y (s i))/2*(Z i)^2)
        else 0
    let Poly : ℝ → ℕ → Ω → ℝ := fun δ m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0)+1)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0)*Δ
      let R : ℕ → ℝ := fun i => X.X (s i+Δ) ω-X.X (s i) ω
      let Z : ℕ → ℝ := fun i => R i-(Δ : ℝ)*X.c
      ∑ i ∈ Finset.range m,
        if (s i < ρ ω ∧ s i+Δ ≤ ρ ω) ∧ δ ≤ |R i|
        then 1+|R i|+(Z i)^2/2 else 0
    ∃ θ K M : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧ 0 ≤ M ∧
      ∀ δ : ℝ, 0 < δ → ∀ m : ℕ, ∀ᵐ ω ∂P,
        max (Large δ m ω) 0 ≤
          (K*Real.exp (θ*B))*
            (∑ i ∈ Finset.range m,
              let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0)+1)
              let s : ℝ≥0 := (i : ℝ≥0)*Δ
              let R : ℝ := X.X (s+Δ) ω-X.X s ω
              if (s < ρ ω ∧ s+Δ ≤ ρ ω) ∧ δ ≤ |R|
              then Real.exp (θ*R) else 0) +
          M*Poly δ m ω := by sorry
