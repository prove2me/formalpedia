-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb38_original_discounted_cashrate_ENNReal_to_real_terminal_budget
-- name    : AvramDividend.Classical.avram_bvb38_original_discounted_cashrate_ENNReal_to_real_terminal_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:05:12.381548+00:00
-- url     : https://prove2.me/theorems/9ee621c4-4615-4f42-acbe-4fe22fd5205c
-- title:
--   Full original HJB discounted ENNReal cash rate plus finite-horizon terminal discount implies exact real compensated cash ceiling
-- statement:
--   Given nonnegative actual source discount q, Lévy negative-mark intensity m, boundary candidate value w, positive physical discount mass c, terminal exponential factor e satisfying the original finite-horizon clock q*c+e=1, any extended-nonnegative Stieltjes cash bounded by ((q+m)*w) times the full physical discounted mass has finite real value and obeys cash.toReal+e*w≤w+m*w*c. Explicit proof of finite ENNReal product prevents collapsing infinite cash to zero under ENNReal.toReal. Directly discharges the scalar step in original full positive-time zero-reserve survivor 254953dc under already-Proved source positive-time cash rate 91d1e73f.
-- source:
--   Authoritative Proved 91d1e73f original full discounted cash HJB rate and Proved 5ce1f298 original finite discount identity.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb38_original_discounted_cashrate_ENNReal_to_real_terminal_budget
    (cash : ℝ≥0∞) (q m w c e : ℝ)
    (hq : 0 ≤ q) (hm : 0 ≤ m) (hw : 0 ≤ w) (hc : 0 ≤ c)
    (hClock : q * c + e = 1)
    (hCash : cash ≤ ENNReal.ofReal ((q + m) * w) * ENNReal.ofReal c) :
    cash.toReal + e * w ≤ w + m * w * c := by sorry
