-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_discounted_stieltjes_cell_ge_right_endpoint_discount_mass
-- name    : AvramDividend.Classical.avram_wave5_04b_discounted_stieltjes_cell_ge_right_endpoint_discount_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:38:44.609703+00:00
-- url     : https://prove2.me/theorems/4bfd2714-dbb5-4da0-89c5-8216ba98b56c
-- title:
--   Right-endpoint exponential discount lower envelope for arbitrary complete Stieltjes cell measure
-- statement:
--   For any measure on the real time line, nonnegative discount q and half-open interval (a,b], the true lower integral of exp(-q s) against the entire measure is at least exp(-q b) times its exact cell mass. No density, atomicity, finiteness or positivity-of-time assumptions; used with the companion Proved left-endpoint upper envelope to squeeze weighted Stieltjes variation under partition refinement.
-- source:
--   Pinned Mathlib lintegral_const, lintegral_mono_ae and ae_restrict_mem; exponential monotonicity and q≥0; companion to Proved left-discount envelope 00b4947d-7c3c-4de6-9058-20912eb4c747.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_discounted_stieltjes_cell_ge_right_endpoint_discount_mass
    (q : ℝ) (hq : 0 ≤ q) (μ : Measure ℝ) (a b : ℝ) :
    ENNReal.ofReal (Real.exp (-(q * b))) * μ (Ioc a b) ≤
      (∫⁻ s in Ioc a b, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) := by sorry
