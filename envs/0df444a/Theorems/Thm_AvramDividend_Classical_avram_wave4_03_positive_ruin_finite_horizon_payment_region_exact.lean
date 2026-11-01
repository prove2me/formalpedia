-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_positive_ruin_finite_horizon_payment_region_exact
-- name    : AvramDividend.Classical.avram_wave4_03_positive_ruin_finite_horizon_payment_region_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:12:16.45198+00:00
-- url     : https://prove2.me/theorems/e662362c-4234-4705-9451-8479a3ca43f8
-- title:
--   Exact finite-horizon positive-ruin payment region switches from closed to strict terminal interval
-- statement:
--   For any finite positive original ruin horizon tau and deterministic finite cutoff T, the exact original paymentTimes tau intersected with real times through T is the *closed* interval [0,T] if T<tau, retaining the right payment atom at T, and the *half-open* interval [0,tau) if T≥tau, excluding the right atom at ruin. The theorem is a genuine set equality, so it rewrites arbitrary weighted full Stieltjes rewards (including e^{-qt}), not just unweighted masses, and retains diffuse and singular-continuous payments. This is a terminal stopping-set interface, not Lévy compensation or Dynkin's formula.
-- source:
--   Canonical paymentTimes_eq_strict_of_pos 7c01995b-bd0b-43b0-bb5e-3a05fb37de5b; original Proposition 4(i) strict pre-ruin payment convention, Avram–Palmowski–Pistorius (2007).

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_strict_of_pos

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_positive_ruin_finite_horizon_payment_region_exact
    (τ T : ℝ≥0) (hτ : 0 < τ) :
    paymentTimes (τ : ℝ≥0∞) ∩ Set.Iic (T : ℝ) =
      if T < τ then Set.Icc (0 : ℝ) (T : ℝ)
      else Set.Ico (0 : ℝ) (τ : ℝ) := by sorry
