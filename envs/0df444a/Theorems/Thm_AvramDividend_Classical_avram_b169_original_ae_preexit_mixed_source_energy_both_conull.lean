-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b169_original_ae_preexit_mixed_source_energy_both_conull
-- name    : AvramDividend.Classical.avram_b169_original_ae_preexit_mixed_source_energy_both_conull
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T22:45:27.04274+00:00
-- url     : https://prove2.me/theorems/9076046d-b5d6-4a93-bac1-2fd56499bd5f
-- title:
--   Original pre-ruin pre-upcross physical mixed source mesh energy with both jumpfree-cell identities and Poisson counts only almost everywhere
-- statement:
--   For the actual original spectrally negative Levy process, arbitrary finite physical source grid cells with endpoints before original source upcrossing and lower-bounded pre-ruin source reserve, construct the compact original physical source increment envelope as in the Proved B67 and B68 results. Assume the selected negative marked-grid count is dominated by the original full Poisson negative source count almost everywhere, and the intrinsic Gaussian plus signed drift identity for each unmarked physical cell is also valid only almost everywhere. The prepared B157 original mixed-source finite-mesh energy theorem handles both conull premises correctly and provides integrability and uniform Gaussian and jump contact expected bound; the remaining original pre-upcross source compact arithmetic is unchanged from Proved B68. This is the conull source-corrected original pre-ruin Ito mesh localisation bound, directly suitable for the genuine original Jsmall source Gaussian drift limit and B159 unmarked cell classification. Publish only when B157 is Proved.
-- source:
--   Prepared direct B157 original two-conull-event mixed Gaussian and negative marked source energy, Proved B67 physical pre-upcross compact source envelope.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_b60_original_compact_jumpless_gaussian_jumpcell_square_split
import Theorems.Thm_AvramDividend_Classical_avram_b58_original_selected_negative_jump_cells_uniform_count_L1
import Theorems.Thm_AvramDividend_Classical_avram_b157_original_mixed_source_energy_conull_jumpfree_and_poisson
import Theorems.Thm_AvramDividend_Classical_avram_b67_original_preupper_X_centered_cell_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original pre-ruin strict interior stopped source has uniform mixed energy under conull marked-grid count domination. -/

theorem AvramDividend.Classical.avram_b169_original_ae_preexit_mixed_source_energy_both_conull
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (V : ℕ → Ω → ℝ) (J : Ω → Finset ℕ)
    (x b d : ℝ) (hxb : 0 ≤ x + b)
    (hCell : ∀ ω i, i ∈ S → s i ω ≤ t i ω ∧ t i ω ≤ T)
    (hLower : ∀ ω i, i ∈ S →
      -x ≤ X.X (s i ω) ω ∧ -x ≤ X.X (t i ω) ω)
    (hBeforeUp : ∀ ω i, i ∈ S →
      (s i ω : ℝ≥0∞) < twoSidedExitUpTime X b ω ∧
      (t i ω : ℝ≥0∞) < twoSidedExitUpTime X b ω)
    (hJsub : ∀ ω, J ω ⊆ S)
    (hJmeas : Measurable (fun ω : Ω => ((J ω).card : ℝ)))
    (hJdom : ∀ᵐ ω ∂P, ((J ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal)
    (hNoJump : ∀ᵐ ω ∂P, ∀ i, i ∈ S → i ∉ J ω →
      X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c =
          V i ω + d * ((t i ω - s i ω : ℝ≥0) : ℝ))
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
        (x + b + (T : ℝ) * |X.c|)^2 * ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal := by sorry
