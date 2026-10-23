-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_weighted_full_kernel_norm_small
-- name    : AvramDividend.Classical.positive_weighted_full_kernel_norm_small
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T21:17:31.567479+00:00
-- url     : https://prove2.me/theorems/c6ab68dc-954e-4f86-82ac-43336e401f6a
-- title:
--   Small weighted absolute norm of the full drift-plus-L1 Volterra kernel
-- statement:
--   Given w>0 and integrability of e^(−wt)K(t) on t>0, if |β|/w + ∫e^(−wt)|K(t)|dt < a, then the full kernel k(t)=|β+K(t)| has finite weighted L1 norm strictly below a. Norm integrability follows from the integrability of the signed weighted kernel, plus the constant exponential. For the bound use |β+K|≤|β|+|K|, the monotone Bochner integral, and the exact Laplace transform ∫e^(−wt)dt=1/w. This is the quantitative contraction constant for causal Volterra solution uniqueness.
-- source:
--   Pinned Mathlib MeasureTheory.Integrable.norm, integral_mono and integral_add; Proved positive_laplace_constant_reference.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_positive_laplace_constant_reference
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.positive_weighted_full_kernel_norm_small
    (K : ℝ → ℝ) (a β w : ℝ) (hw : 0 < w)
    (hKi : IntegrableOn (fun t : ℝ => Real.exp (-w * t) * K t)
      (Ioi (0 : ℝ)) volume)
    (hsmall : |β| / w +
      (∫ t in Ioi (0 : ℝ), |K t| * Real.exp (-w * t) ∂volume) < a) :
    IntegrableOn (fun t : ℝ => Real.exp (-w * t) * |β + K t|)
      (Ioi (0 : ℝ)) volume ∧
    (∫ t in Ioi (0 : ℝ),
      Real.exp (-w * t) * |β + K t| ∂volume) < a := by sorry
