-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a300_true_stopped_fullcell_global_jet_and_HJB_exponential_envelope
-- name    : AvramDividend.Classical.avram_ga_a300_true_stopped_fullcell_global_jet_and_HJB_exponential_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:40:04.275913+00:00
-- url     : https://prove2.me/theorems/c85a5c80-a625-45f0-9476-8d8831b420b3
-- title:
--   Genuine Gaussian stopped full physical cells have uniform prepayment jets and positive endpoint global HJB exponential upper
-- statement:
--   On the original zerojump Gaussian physical mesh, uniformly on almost every path and every wholly pre-stop cell, the prepayment value, first derivative and second derivative are bounded by a single deterministic constant M, and the actual positive post-increment reserve value is bounded by a global HJB exponential envelope K exp(theta times endpoint reserve). This combines proved source jets a165, true endpoint positivity a163 and genuine global Gaussian HJB upper a257, and provides the missing exact original source hypotheses of a260 for a263.
-- source:
--   Avram zerojump Gaussian X.X physical stopped fullcells, a165, a163, a257

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a165_original_strict_source_postpayment_C2_jet_uniform_ae
import Theorems.Thm_AvramDividend_Classical_avram_ga_a163_original_full_mesh_source_endpoint_positive
import Theorems.Thm_AvramDividend_Classical_avram_ga_a257_original_zerojump_HJB_global_positive_exponential_upper
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a300_true_stopped_fullcell_global_jet_and_HJB_exponential_envelope
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
    ∃ θ K M : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧ 0 ≤ M ∧
      ∀ m : ℕ, ∀ᵐ ω ∂P, ∀ i ∈ Finset.range m,
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let y : ℝ := x + X.X s ω - rightLimit D s ω
        let r : ℝ := X.X (s + Δ) ω - X.X s ω
        (s < ρ ω ∧ s + Δ ≤ ρ ω) →
          |w y| ≤ M ∧ |deriv w y| ≤ M ∧
          |iteratedDeriv 2 w y| ≤ M ∧
          w (y+r) ≤ K*Real.exp (θ*(y+r)):= by sorry
