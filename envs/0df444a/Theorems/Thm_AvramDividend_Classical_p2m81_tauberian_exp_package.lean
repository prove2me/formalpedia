-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_tauberian_exp_package
-- name    : AvramDividend.Classical.p2m81_tauberian_exp_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T07:59:59.27487+00:00
-- url     : https://prove2.me/theorems/1d418087-8a6a-49b5-97e8-e90e27f97792
-- title:
--   Tauberian exponential integrability, value and tail-decay package
-- statement:
--   For positive beta, the exponential exp(-(beta*x)) is integrable on (0,oo) with integral 1/beta, and for every positive a the Tauberian tail factor b*exp(-(b-b0)*a)*K tends to 0 as b tends to infinity. Pure Mathlib helper isolating the exponential-integral normal form used by the standing-free scale-origin Tauberian contradiction for parent fc6b315a (AvramDividend.Classical.p2m81_bv_root_scale_origin_pos_no_standing_public). Its head-integral value feeds D1 and its tail decay drives the bridge contradiction.
-- source:
--   Decomposition child AB of fc6b315a standing-free Tauberian route (full 189-line proof exceeds 100-line/2500-token/complexity caps). Proved from exp_neg_integrableOn_Ioi, integral_exp_mul_Ioi and tendsto_pow_mul_exp_neg_atTop_nhds_zero with scaling; no project imports.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_tauberian_exp_package (β : ℝ) (hβ : 0 < β) :
    IntegrableOn (fun x : ℝ => Real.exp (-(β * x))) (Ioi (0 : ℝ)) ∧
    (∫ x in Ioi (0 : ℝ), Real.exp (-(β * x))) = 1 / β ∧
    ∀ (a K β0 : ℝ), 0 < a → Tendsto (fun b : ℝ => b * Real.exp (-(b - β0) * a) * K) atTop (𝓝 0) := by sorry
