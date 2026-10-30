-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_finite_ennreal_record_product_limit
-- name    : AvramDividend.Classical.avram_ws01h_finite_ennreal_record_product_limit
-- status  : Open
-- author  : @WillR
-- created : 2026-10-29T20:34:23.325783+00:00
-- url     : https://prove2.me/theorems/6af3b323-3392-4506-9b69-903a7f8f4f22
-- title:
--   Exact finite-limit genuine Esscher Qp killed first-record regeneration product survives positive-rate limit in extended nonnegative reals
-- statement:
--   For actual nonnegative finite-rate quantities f_n (killed original Lévy first-record terminal Qp mass), g_n (fresh genuine Qp survival CDF) and h_n (original killed stopped Esscher discount), if f_n = c (g_n h_n) holds at every observation rate and f_n→Cx, g_n→Ca, h_n→K, where c,Ca,K are genuinely finite, then the perpetual source CDF satisfies Cx=c(Ca K). The proof uses only pinned Mathlib's ENNReal.Tendsto.mul and ENNReal.mul_ne_top at explicit finite limits to prevent spurious ∞×0 behavior, and uniqueness of limits in the Hausdorff topology. This is the exact final probabilistic-renewal product limit lemma needed to combine accepted source first-record Qp regeneration, actual killed-mass CDF convergence and original P q+p→q discount continuity without assuming the scale ratio.
-- source:
--   Pinned Mathlib ENNReal.Tendsto.mul (Mathlib.Topology.Instances.ENNReal.Lemmas), ENNReal.mul_ne_top, tendsto_nhds_unique, source true Qp CDF and stopped reward finite bounds.

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Data.ENNReal.Operations

open Filter
open scoped ENNReal Topology

theorem AvramDividend.Classical.avram_ws01h_finite_ennreal_record_product_limit
    (f g h : ℕ → ℝ≥0∞) (c Cx Ca K : ℝ≥0∞)
    (hc : c ≠ ⊤) (hCa : Ca ≠ ⊤) (hK : K ≠ ⊤)
    (hf : Tendsto f atTop (𝓝 Cx))
    (hg : Tendsto g atTop (𝓝 Ca))
    (hh : Tendsto h atTop (𝓝 K))
    (hfactor : ∀ n : ℕ, f n = c * (g n * h n)) :
    Cx = c * (Ca * K) := by sorry
