-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_preruin_full_grid_right_endpoint_mesh_budget
-- name    : AvramDividend.Classical.avram_wave6_08_original_preruin_full_grid_right_endpoint_mesh_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:45:39.903135+00:00
-- url     : https://prove2.me/theorems/b0ef57b5-3d2a-4215-b332-9ee03f0cdc5e
-- title:
--   Complete original pre-ruin source finite-grid Stieltjes right-endpoint bound with uniform total mesh mass error
-- statement:
--   For an actual spectrally negative Lévy reserve and genuine admissible dividend path, every chronological pre-ruin finite grid with maximum cell width m has the full exponentially discounted Stieltjes integral bounded by the sum of right-endpoint discounted source-frozen cap-linear value drops, plus q*m times the dividendMeasure mass of the entire interval. The full measure partition includes singular-continuous variation and atomic dividend payments. The bound is deterministic and source-specific, and is used to pass to a fine stopped grid without omitting boundary contacts.
-- source:
--   Exact Proved original source right-endpoint cell quantitative bound 4bcce380... plus canonically Proved complete Stieltjes half-open-cell partition 947adc6d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_positive_cap_original_right_endpoint_stieltjes_error
import Theorems.Thm_AvramDividend_Classical_lintegral_Ioc_partition_fin

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave6_08_original_preruin_full_grid_right_endpoint_mesh_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (u : ℕ → ℝ≥0) (hu : Monotone u)
    (n : ℕ) (m : ℝ) (hm : 0 ≤ m)
    (hmesh : ∀ i < n, ((u (i + 1) : ℝ) - (u i : ℝ)) ≤ m)
    (hPre : ∀ i < n,
      u (i + 1) = 0 ∨ (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Ioc (u 0 : ℝ) (u n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      (∑ i ∈ Finset.range n,
        ENNReal.ofReal (Real.exp (-(q * (u (i + 1) : ℝ)))) *
          ENNReal.ofReal
            (V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
              V (x + X.X (u (i + 1)) ω -
                rightLimit D (u (i + 1)) ω))) +
      ENNReal.ofReal (q * m) *
        dividendMeasure D ω (Ioc (u 0 : ℝ) (u n : ℝ)) := by sorry
