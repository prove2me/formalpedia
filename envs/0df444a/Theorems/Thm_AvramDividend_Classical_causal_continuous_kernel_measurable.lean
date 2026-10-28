-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_continuous_kernel_measurable
-- name    : AvramDividend.Classical.causal_continuous_kernel_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T16:41:03.568596+00:00
-- url     : https://prove2.me/theorems/0baaa6d9-b33a-43ac-a4dc-54c72809181c
-- title:
--   Causal positive-time continuous kernels are measurable globally
-- statement:
--   Every real kernel continuous at strictly positive times and identically zero on nonpositive times is measurable on the entire real line, even if it is unbounded near zero. This is the causal kernel measurability bridge required to combine L1 signed convolution powers with the pointwise Neumann-series envelope induction.
-- source:
--   The kernel agrees everywhere with the piecewise function equal to k on (0,∞) and 0 on its complement. The pinned ContinuousOn.measurable_piecewise theorem applies to the positive-time continuity and constant continuity on the complement. This supplies hkmeas of causal_l1_measurable_signed_products for signed Gaussian kernels with possible integrable singularity at zero.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.ContinuousOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_continuous_kernel_measurable
    (k : ℝ → ℝ)
    (hkcont : ContinuousOn k (Ioi (0 : ℝ)))
    (hkzero : ∀ x : ℝ, x ≤ 0 → k x = 0) :
    Measurable k := by sorry
