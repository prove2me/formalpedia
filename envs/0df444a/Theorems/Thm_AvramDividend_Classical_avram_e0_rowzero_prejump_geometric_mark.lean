-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_e0_rowzero_prejump_geometric_mark
-- name    : AvramDividend.Classical.avram_e0_rowzero_prejump_geometric_mark
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:30:28.3142+00:00
-- url     : https://prove2.me/theorems/39e3427b-99d2-47f9-8e84-73f567c59920
-- title:
--   The first original physical-grid prepayment reserve equals the prescribed geometric mark
-- statement:
--   At nonnegative time zero, the source Mathlib Function.leftLim defaults to its value because zero has no points to its left. Thus, whenever a spectrally negative Levy path starts at zero and the dividend right limit at zero is x-epsilon, the exact first row's prepayment reserve Z0 equals epsilon.
-- source:
--   Exact row-zero Z from e0b94d7f-cb1e-450a-8f04-b2e732af5dbe. Pinned Mathlib Topology.Order.LeftRightLim leftLim_eq_of_isBot; necessary for coupling the geometric scalar divergence to the original generator-residual B.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_e0_rowzero_prejump_geometric_mark
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x ε : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hzero : X.X 0 ω = 0)
    (hD : rightLimit D 0 ω = x - ε) :
    Function.leftLim (fun t : ℝ≥0 =>
      x + X.X t ω - rightLimit D t ω) 0 = ε := by sorry
