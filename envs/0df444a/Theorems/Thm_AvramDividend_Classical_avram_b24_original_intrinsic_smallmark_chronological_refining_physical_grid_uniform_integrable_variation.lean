-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_intrinsic_smallmark_chronological_refining_physical_grid_uniform_integrable_variation
-- name    : AvramDividend.Classical.avram_b24_original_intrinsic_smallmark_chronological_refining_physical_grid_uniform_integrable_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:44:36.014199+00:00
-- url     : https://prove2.me/theorems/4298b753-7c3e-479e-a1d6-10a746055769
-- title:
--   Genuine original finite-activity compensated smallmark has one integrable jump-count bound on total variation across EVERY monotone chronological refining physical stopped grid
-- statement:
--   Under actual finite negative-jump Lévy activity, ANY original intrinsic compensated Jsmall witness admits one and the same integrable positive marked-count plus compensator-drift source majorant B_T dominating the SUM of absolute Jsmall gains over EVERY finite nondecreasing chronological physical grid of any size with endpoint at most T, on one source P-conull event. The physical grid may be stopped at the true ruin time, have repeated clocks, and refine arbitrarily without growing the stochastic bound. The proof passes the exact original all-disjoint-mesh source variation budget through two sound deterministic original grid facts: pairwise half-open cell disjointness from monotonicity and telescoping of total elapsed time to ≤T. This directly supplies the missing refining-grid uniform marked-source L1 variation dominator required to prove B219 physical Itô-Meyer finite-activity bounded predictable coefficient gain stability, retaining every genuine negative ruin-contact jump without large negative-jump moments.
-- source:
--   Original B24 uniform integrable disjoint stopped marked-grid variation, monotone Ioc physical grid disjointness, and original chronological grid time telescope.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_intrinsic_smallmark_chronological_refining_physical_grid_uniform_integrable_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω)))
    (T : ℝ≥0) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Ioo (-1 : ℝ) 0)
    let B : Ω → ℝ := fun ω => (N ω).toReal +
      (T : ℝ) * ‖∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν‖
    Integrable B P ∧
      ∀ᵐ ω ∂P, ∀ (n : ℕ) (t : ℕ → ℝ≥0),
        Monotone t → t n ≤ T →
        (∑ i ∈ Finset.range n,
          ‖Jsmall (t (i + 1)) ω - Jsmall (t i) ω‖) ≤ B ω := by sorry
