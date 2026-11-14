-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b157_original_mixed_source_energy_conull_jumpfree_and_poisson
-- name    : AvramDividend.Classical.avram_b157_original_mixed_source_energy_conull_jumpfree_and_poisson
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T21:02:24.65267+00:00
-- url     : https://prove2.me/theorems/2a8e3961-604f-4fd2-beed-654eb6683024
-- title:
--   Original finite mixed Gaussian and negative-mark mesh energy requires the jumpfree source identity and Poisson cardinal domination only on conull events
-- statement:
--   For the true original finite-negative-activity spectrally negative Levy source and arbitrary finite possibly random physical mesh intervals, suppose the marked-cell count is dominated almost everywhere by the original negative Poisson source count and, on another conull event, the unmarked physical source increments admit the intrinsic Gaussian residual plus signed drift decomposition. Assume the marked compact source bound and measurable/integrable Gaussian and duration energy envelopes. The Proved original B60 compact pathwise mixed square inequality can be applied to the conull set of paths satisfying all unmarked cell source identities; its consequence is an almost-everywhere energy bound, sufficient for integrability and expectation comparison by integral_mono_ae. Proved original JA35 supplies the true full negative source count L1 and its intensity first moment to control the marked-cell term. Thus the same mesh-uniform original source mixed square-energy estimate holds with both physical jumpfree and negative mark count assumptions only almost everywhere, preserving exceptional paths and allowing direct use of original B146 conull source decomposition rather than the physically unjustified older all-path hNoJump assumption.
-- source:
--   Proved original B60 pathwise source square bound on an arbitrary conull set and Proved original JA35 negative Poisson source first moment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b60_original_compact_jumpless_gaussian_jumpcell_square_split
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original mixed finite Gaussian and marked-grid mesh square-energy bound with only conull source count domination. -/

theorem AvramDividend.Classical.avram_b157_original_mixed_source_energy_conull_jumpfree_and_poisson
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (V : ℕ → Ω → ℝ) (J : Ω → Finset ℕ)
    (d a b : ℝ) (hab : a ≤ b) (hJsub : ∀ ω, J ω ⊆ S)
    (hJmeas : Measurable (fun ω : Ω => ((J ω).card : ℝ))) (hJdom : ∀ᵐ ω ∂P, ((J ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal)
    (hNoJump : ∀ᵐ ω ∂P, ∀ i, i ∈ S → i ∉ J ω → X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c = V i ω + d * ((t i ω - s i ω : ℝ≥0) : ℝ))
    (hJump : ∀ ω i, i ∈ S → i ∈ J ω → |X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c| ≤ b - a)
    (hEmeas : Measurable (fun ω => ∑ i ∈ S,
      (X.X (t i ω) ω - X.X (s i ω) ω - ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c)^2))
    (hGI : Integrable (fun ω => ∑ i ∈ S, (V i ω)^2) P)
    (hDI : Integrable (fun ω => ∑ i ∈ S, (((t i ω - s i ω : ℝ≥0) : ℝ))^2) P) :
    let E : Ω → ℝ := fun ω => ∑ i ∈ S,
      (X.X (t i ω) ω - X.X (s i ω) ω - ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c)^2
    let G : Ω → ℝ := fun ω => ∑ i ∈ S, (V i ω)^2
    let D : Ω → ℝ := fun ω => ∑ i ∈ S, (((t i ω - s i ω : ℝ≥0) : ℝ))^2
    Integrable E P ∧ (∫ ω, E ω ∂P) ≤
      2 * (∫ ω, G ω ∂P) + 2 * d^2 * (∫ ω, D ω ∂P) +
        (b-a)^2 * ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal := by sorry
