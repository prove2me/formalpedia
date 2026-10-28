-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_exponent_gap_div_tendsto_zero
-- name    : AvramDividend.Classical.bv_exponent_gap_div_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:19:51.989007+00:00
-- url     : https://prove2.me/theorems/fc81170b-78b0-4a76-922f-8c365f750f8d
-- title:
--   Bounded-variation Lévy Laplace exponent has physical-drift asymptotic slope
-- statement:
--   For any bounded-variation spectrally negative Lévy process, the canonical physical-drift-normalised Laplace exponent satisfies (drift*theta - psi(theta))/theta -> 0 as theta tends to positive infinity. Use the accepted exact exponent-integral identity and the full negative-jump dominated-convergence theorem, with the integrable truncated first negative-jump moment supplied by the bounded-variation assumptions. This is the exponent asymptotic required for the finite-mesh proof that infinitely active negative jumps preclude any nondecreasing initial path interval.
-- source:
--   Proved bv_exponent_negative_jump_deficit_exact and chat07_bv_negative_jump_min_abs_integrable; full negative-jump normalised integral helper.

import Theorems.Thm_AvramDividend_Classical_negative_jump_full_normalized_exp_deficit_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_chat07_bv_negative_jump_min_abs_integrable
import Theorems.Thm_AvramDividend_Classical_bv_exponent_negative_jump_deficit_exact
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.Filter.Tendsto

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_exponent_gap_div_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    Tendsto (fun θ : ℝ => (X.drift * θ - X.ψ θ) / θ)
      atTop (nhds (0 : ℝ)) := by sorry
