-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_positive_discount_scale_exists_from_zero
-- name    : AvramDividend.Classical.unbounded_positive_discount_scale_exists_from_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:49:23.74362+00:00
-- url     : https://prove2.me/theorems/636cfffe-3c5a-4e91-a030-4d95f9ee9065
-- title:
--   Construct every positive-discount scale from an unbounded-variation zero-discount scale
-- statement:
--   Given an unbounded-variation spectrally negative Lévy process and a zero-discount IsScaleFunction witness, construct a q-scale function for each q>0 using the positive causal Neumann series Wq=sum(n≥0,q^n W0^{*(n+1)}). The proof must establish support on x<0, nonnegativity, continuity through the zero origin, monotonicity and every admissible Laplace identity. Exponential damping at θ with q<ψ(θ) gives a strict L1 contraction, geometric convolution-power mass, and uniform convergence via a bounded-kernel L∞-L1 estimate. The previously published geometric Laplace identity identifies the transform.
-- source:
--   Behme, Oechsler & Schilling (2022), arXiv:2109.09359, scale convolution series. Existing Proved scaleFunction_global_weighted_norm_bddAbove, causal_l1_convolution_power_exact_mass_geometric, causal_neumann_geometric_series_continuousOn_nonnegative, scale_renewal_laplace_geometric_series, chat04_psi_eventually_gt_of_unbounded_variation, unbounded_scale_zero_origin_nonnegative_discount.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_positive_discount_scale_exists_from_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (q : ℝ) (hq : 0 < q) :
    ∃ Wq : ℝ → ℝ, IsScaleFunction X q Wq := by sorry
