-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_public_canonical_strict_stieltjes_real_error_sandwich
-- name    : AvramDividend.Classical.avram_jump6_B_public_canonical_strict_stieltjes_real_error_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:31:19.13634+00:00
-- url     : https://prove2.me/theorems/1266dcaf-581e-4ded-8f30-3885a1552532
-- title:
--   Original stopped canonical clipped Stieltjes quadrature real error nonnegative and bounded by shrinking discount mesh
-- statement:
--   For each fixed path before ruin and the original admissible dividend measure, the canonical clipped grid quadrature cash discount error is nonnegative and at most q times the grid width times the original finite dividend mass. This is an exact source statement, retaining paymentTimes, nonnegative clock, Ioc and true rightLimit D increments. Proving it plus the public mesh-width limit yields the full canonical zero-error theorem.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_discount_mesh_error_tends_zero
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_grid_reaches_bounded_clock_every_mesh
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_public_canonical_strict_stieltjes_real_error_sandwich
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (t : ℝ≥0) (n : ℕ) (ht : t ≤ (n : ℝ≥0))
    (hStrict : (t : ℝ≥0∞) < ruinTime X x D ω) :
    let N : ℕ → ℕ := fun j => (n + 1) * (j + 1)
    let v : ℕ → ℕ → ℝ≥0 := fun j i =>
      min ((i : ℝ≥0) * ((1 : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0))) t
    let err : ℕ → ℝ := (fun j : ℕ =>
      ∑ i ∈ Finset.range (N j),
        ((∫⁻ r in paymentTimes (ruinTime X x D ω) ∩
            Ioc (v j i : ℝ) (v j (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * r)))
            ∂(dividendMeasure D ω)).toReal -
          Real.exp (-(q * (v j (i + 1) : ℝ))) *
            (rightLimit D (v j (i + 1)) ω - rightLimit D (v j i) ω)))
    ∀ j : ℕ, 0 ≤ err j ∧ err j ≤ (q / ((j : ℝ) + 1)) * (rightLimit D t ω - rightLimit D 0 ω) := by sorry
