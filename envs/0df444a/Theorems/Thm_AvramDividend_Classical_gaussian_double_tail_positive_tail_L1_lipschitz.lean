-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_positive_tail_L1_lipschitz
-- name    : AvramDividend.Classical.gaussian_double_tail_positive_tail_L1_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T20:42:44.256436+00:00
-- url     : https://prove2.me/theorems/7816877b-aeca-4880-9f29-cf2fb32dd713
-- title:
--   Finite L1 time-Lipschitz bound for Gaussian double-tail atoms on positive jump tails
-- statement:
--   Given a positive lower cutoff epsilon and time arguments s,t at least epsilon, the L1 difference of the conditional Gaussian Esscher double-tail atom kernels is at most |t-s| times the finite Esscher-weighted jump tail mass. This quantitative bound converts the accepted pointwise Lipschitz inequality and finite positive-tail measure estimate into a continuity ingredient for the Volterra kernel.
-- source:
--   Uses Proved gaussian_double_tail_conditional_atom_lipschitz and gaussian_esscher_positive_tail_weight_finite; pinned ENNReal.ofReal_mul and lintegral_const_mul.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_positive_tail_L1_lipschitz
    (μ : Measure ℝ) (ε φ s t : ℝ)
    (hε : 0 < ε) (hφ : 0 < φ)
    (hs : ε ≤ s) (ht : ε ≤ t)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ z in Ici ε, ENNReal.ofReal
      (|(if 0 < t ∧ t < z then (z - t) * Real.exp (-φ * z) else 0) -
        (if 0 < s ∧ s < z then (z - s) * Real.exp (-φ * z) else 0)|) ∂μ) ≤
    ENNReal.ofReal (|t - s|) *
      (∫⁻ z in Ici ε, ENNReal.ofReal (Real.exp (-φ * z)) ∂μ) ∧
    ENNReal.ofReal (|t - s|) *
      (∫⁻ z in Ici ε, ENNReal.ofReal (Real.exp (-φ * z)) ∂μ) < ⊤ := by sorry
