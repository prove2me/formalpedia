-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b151_original_ae_preexit_mixed_gaussian_negative_energy_from_direct
-- name    : AvramDividend.Classical.avram_b151_original_ae_preexit_mixed_gaussian_negative_energy_from_direct
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T21:00:19.681301+00:00
-- url     : https://prove2.me/theorems/e9ff833d-b6b3-4a3c-b397-85eac9fc9080
-- title:
--   Original pre-ruin pre-upcross stopped mixed Gaussian and negative marked-cell source energy under conull domination via direct B150
-- statement:
--   In true original stopped physical cells before ruin and the original spatial source upcrossing, keep the accepted B68 original compact pathwise envelope construction using Proved B67 and all genuine clock endpoints. Replace its all-sample selected marked Poisson domination by almost-everywhere source domination through the direct mixed-energy B150 estimate. This proves the same original stopped finite-mesh Gaussian and negative physical mark squared-energy integrability and uniform mean bound, with exceptional infinite negative-mark counts only on null paths. It gives a direct B150 successor towards the original JB27 positive-clock Ito source certificate. Wait until B150 is Proved before publication.
-- source:
--   Prepared B150 direct conull original mixed mesh energy and Proved B67 true original preexit source compact bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_b60_original_compact_jumpless_gaussian_jumpcell_square_split
import Theorems.Thm_AvramDividend_Classical_avram_b58_original_selected_negative_jump_cells_uniform_count_L1
import Theorems.Thm_AvramDividend_Classical_avram_b150_original_direct_ae_mixed_gaussian_negative_mesh_energy
import Theorems.Thm_AvramDividend_Classical_avram_b67_original_preupper_X_centered_cell_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original pre-ruin strict interior stopped source has uniform mixed energy under conull marked-grid count domination. -/

theorem AvramDividend.Classical.avram_b151_original_ae_preexit_mixed_gaussian_negative_energy_from_direct
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
    (hNoJump : ∀ ω i, i ∈ S → i ∉ J ω →
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
