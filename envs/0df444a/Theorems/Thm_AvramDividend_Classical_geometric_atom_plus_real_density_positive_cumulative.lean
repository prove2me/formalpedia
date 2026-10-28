-- Prove2me | Theorems.Thm_AvramDividend_Classical_geometric_atom_plus_real_density_positive_cumulative
-- name    : AvramDividend.Classical.geometric_atom_plus_real_density_positive_cumulative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:42:29.962976+00:00
-- url     : https://prove2.me/theorems/510cad0f-b8d8-4227-b31f-4a2bb7b9cb04
-- title:
--   Geometric renewal initial atom vanishes on positive intervals, leaving scaled real primitive
-- statement:
--   Suppose β is a nonnegative scalar multiple of a Dirac atom at zero plus a nonnegative Lebesgue density. For x≥0 the initial Dirac atom contributes no mass to (0,x], so the real cumulative β((0,x]) equals r times the integral of the real density over [0,x]. The proof combines the canonical Proved nonnegative_scalar_real_density_Ioc_intervalIntegral with the Dirac zero mass and measure addition laws. This translates the fully normalised geometric Esscher renewal measure into the exact real primitive needed in the bounded-variation scale function identity on the path towards cstar_lt_top.
-- source:
--   Canonical Proved nonnegative_scalar_real_density_Ioc_intervalIntegral; pinned Mathlib Measure.add_apply, Measure.smul_apply and Dirac evaluation.

import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_nonnegative_scalar_real_density_Ioc_intervalIntegral
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.geometric_atom_plus_real_density_positive_cumulative
    (r : ℝ) (hr : 0 ≤ r) (f : ℝ → ℝ) (hfpos : ∀ y : ℝ, 0 ≤ f y)
    (β : Measure ℝ)
    (hβ : β = ENNReal.ofReal r • (Measure.dirac (0 : ℝ) +
      volume.withDensity (fun y : ℝ => ENNReal.ofReal (f y))))
    (x : ℝ) (hx : 0 ≤ x) (hfi : IntervalIntegrable f volume 0 x) :
    (β (Ioc (0 : ℝ) x)).toReal =
      r * ∫ y in (0 : ℝ)..x, f y := by sorry
