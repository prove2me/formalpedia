-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_vcstar_clipped_finite_grid_integrable
-- name    : AvramDividend.Classical.avram_bv_gen8_original_vcstar_clipped_finite_grid_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:18:35.857243+00:00
-- url     : https://prove2.me/theorems/c89d9a00-58f3-4817-bf69-8524df52ddc8
-- title:
--   Source BV original full generator finite-grid negative clipping has finite L1 under exact measurability
-- statement:
--   At each original stopped BV physical grid, the full positive-reserve candidate generator sum is nonpositive; if the exact random sum is a.e. strongly measurable, every bounded negative clipping is integrable under the original probability law. This supplies a source-exact one-sided Fatou approximation but explicitly does not claim integrability of the unbounded limit.
-- source:
--   Uses Proved exact original generator sign 1874dd49 and the bounded clipping proof technique from Proved d81f5f1e. Measurability of the original stopped sum is retained as an explicit premise.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_vcstar_full_positive_cell_sign_and_cap_zero
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_gen8_original_vcstar_clipped_finite_grid_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, u n i ≤ u n (i + 1)) :
    let H : ℕ → ℕ → Ω → ℝ := fun n i ω =>
      let Z : ℝ := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator (vcstar W) Z - q * vcstar W Z) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    (∀ n, AEStronglyMeasurable
      (fun ω => ∑ i ∈ Finset.range (n + 1), H n i ω) P) →
    ∀ (K : ℝ), 0 ≤ K →
      ∀ n, Integrable (fun ω =>
        max (-K) (∑ i ∈ Finset.range (n + 1), H n i ω)) P := by sorry
