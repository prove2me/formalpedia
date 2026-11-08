-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_capped_strategy_full_vcstar_grid_L1_without_above_hgen
-- name    : AvramDividend.Classical.avram_bv_gen8_capped_strategy_full_vcstar_grid_L1_without_above_hgen
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:34:15.948784+00:00
-- url     : https://prove2.me/theorems/2be7bf4d-8cfd-4c8e-bea5-064e1e76b863
-- title:
--   Original capped BV full generator grid is zero and integrable without any above-cap HJB hypothesis
-- statement:
--   For an actual admissible dividend strategy capped at the finite positive cstar barrier, prove the entire original stopped physical BV generator grid vanishes and has L1 integrability. Uses unconditional source generator harmonicity strictly below cstar and exactly at cstar; no above-cap generator assumption.
-- source:
--   Direct source-exact strengthening of 24650414 using Proved b196c9ff interior BV harmonicity, 0458283a unconditional cap harmonicity, and a009975c actual original post-right reserve cap. Eliminates hgen without modifying any process or strategy hypotheses.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_gen8_capped_strategy_full_vcstar_grid_L1_without_above_hgen
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
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
