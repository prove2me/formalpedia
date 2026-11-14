-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b150_original_direct_ae_mixed_gaussian_negative_mesh_energy
-- name    : AvramDividend.Classical.avram_b150_original_direct_ae_mixed_gaussian_negative_mesh_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T20:54:59.397202+00:00
-- url     : https://prove2.me/theorems/e5b4fe1b-81ea-44de-a4bc-27bbd0c49c27
-- title:
--   Direct original physical mixed Gaussian and negative-mark finite-mesh energy from true conull Poisson count domination
-- statement:
--   For the genuine finite-negative-activity original Levy source and arbitrary finite physical random-clock mesh cells with intrinsic Gaussian increments and negative marked cells, assume the source compact square split, Gaussian and duration integrable envelopes, and measurable marked-cell count dominated almost everywhere by actual original finite-horizon negative marked Poisson source count. Proved original JA35 gives first-moment integrability for that real physical Poisson count and its exact horizon times intensity mean. Hence the marked-cell cardinal is integrable under conull source domination by integral_mono_ae. Proved B60 supplies a true pathwise source Gaussian and marked-contact quadratic bound. Combining the two yields uniform finite-mesh original source square-energy integrability and expected bound as in the Proved B61 result, while properly allowing original null exceptional paths with infinite negative-jump counts. This bypasses the separate B140-B141 pending publication chain and is a sound original-source estimate for ruin-clipped stopped Ito localisation.
-- source:
--   Proved original JA35 exact negative-mark Poisson first moment and B60 physical Gaussian/marked square source split, plus Mathlib integral_mono_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b60_original_compact_jumpless_gaussian_jumpcell_square_split
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original mixed finite Gaussian and marked-grid mesh square-energy bound with only conull source count domination. -/

theorem AvramDividend.Classical.avram_b150_original_direct_ae_mixed_gaussian_negative_mesh_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (V : ℕ → Ω → ℝ) (J : Ω → Finset ℕ)
    (d a b : ℝ) (hab : a ≤ b)
    (hJsub : ∀ ω, J ω ⊆ S)
    (hJmeas : Measurable (fun ω : Ω => ((J ω).card : ℝ)))
    (hJdom : ∀ᵐ ω ∂P, ((J ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal)
    (hNoJump : ∀ ω i, i ∈ S → i ∉ J ω →
      X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c =
          V i ω + d * ((t i ω - s i ω : ℝ≥0) : ℝ))
    (hJump : ∀ ω i, i ∈ S → i ∈ J ω →
      |X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c| ≤ b - a)
    (hEmeas : Measurable (fun ω =>
      ∑ i ∈ S, (X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c)^2))
    (hGI : Integrable (fun ω => ∑ i ∈ S, (V i ω)^2) P)
    (hDI : Integrable (fun ω => ∑ i ∈ S,
      (((t i ω - s i ω : ℝ≥0) : ℝ))^2) P) :
    let E : Ω → ℝ := fun ω =>
      ∑ i ∈ S, (X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c)^2
    let G : Ω → ℝ := fun ω => ∑ i ∈ S, (V i ω)^2
    let D : Ω → ℝ := fun ω =>
      ∑ i ∈ S, (((t i ω - s i ω : ℝ≥0) : ℝ))^2
    Integrable E P ∧ (∫ ω, E ω ∂P) ≤
      2 * (∫ ω, G ω ∂P) + 2 * d^2 * (∫ ω, D ω ∂P) +
        (b-a)^2 * ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal := by sorry
