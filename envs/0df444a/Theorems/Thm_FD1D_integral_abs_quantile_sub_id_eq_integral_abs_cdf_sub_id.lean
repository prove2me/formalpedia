-- Prove2me | Theorems.Thm_FD1D_integral_abs_quantile_sub_id_eq_integral_abs_cdf_sub_id
-- name    : FD1D.integral_abs_quantile_sub_id_eq_integral_abs_cdf_sub_id
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:39.75152+00:00
-- url     : https://prove2.me/theorems/8efa90e2-85ac-5ade-aa5e-d6e973d5283a
-- title:
--   FD1 D: integral abs quantile sub id eq integral abs cdf sub id
-- statement:
--   The one-dimensional quantile/CDF identity, proved directly by expressing
--   absolute displacement as an integral of threshold disagreements and
--   swapping the two unit-interval integrals.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1522-L1578
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Transport.lean#L1522-L1578

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]

theorem FD1D.integral_abs_quantile_sub_id_eq_integral_abs_cdf_sub_id
    {F T : ℝ → ℝ}
    (_hF : Measurable F) (hT : Measurable T)
    (hF01 : MapsTo F (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hT01 : MapsTo T (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hgc : ∀ u ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (0 : ℝ) 1,
      T u ≤ z ↔ u ≤ F z) :
    (∫ u in Icc (0 : ℝ) 1, |T u - u|) =
      ∫ z in Icc (0 : ℝ) 1, |F z - z| := by sorry
