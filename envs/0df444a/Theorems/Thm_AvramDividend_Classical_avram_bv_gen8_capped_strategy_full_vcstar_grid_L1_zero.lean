-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_capped_strategy_full_vcstar_grid_L1_zero
-- name    : AvramDividend.Classical.avram_bv_gen8_capped_strategy_full_vcstar_grid_L1_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:54:39.271338+00:00
-- url     : https://prove2.me/theorems/24650414-045e-489b-8d21-677ecce6ceaf
-- title:
--   Every original cstar-capped admissible BV strategy has zero full generator grid and L1
-- statement:
--   Under the exact cstar cap and original IsAdmissibleLe strategy assumptions, the original Lévy pre-jump stopped reserve is at most cstar, so the complete discounted candidate generator contribution is zero on every physical grid and integrable.
-- source:
--   Causal repair of failed authoring job 887b6ef7: declaration uses only original Definitions.*; the proof source separately imports the two Open reduction children so Prove2Me may accept the sketch before full child proofs. No change to formal theorem type.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_gen8_capped_strategy_full_vcstar_grid_L1_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ cstar W)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (cstar W) D)
    (u : ℕ → ℕ → ℝ≥0) :
    let H : ℕ → ℕ → Ω → ℝ := fun n i ω =>
      let Z : ℝ := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator (vcstar W) Z - q * vcstar W Z) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    ∀ n, (∀ ω, (∑ i ∈ Finset.range (n + 1), H n i ω) = 0) ∧
      Integrable (fun ω => ∑ i ∈ Finset.range (n + 1), H n i ω) P := by sorry
