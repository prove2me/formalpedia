-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_esscher_tilted_scale_monotone_uniform_bound
-- name    : AvramDividend.Classical.unbounded_esscher_tilted_scale_monotone_uniform_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-21T22:45:08.125859+00:00
-- url     : https://prove2.me/theorems/2e0c71fa-d8e4-453b-8f77-f76c971bd559
-- title:
--   Monotonicity and global upper bound for an Esscher-tilted unbounded-variation scale function
-- statement:
--   For q>0, every supplied positive root φ of ψ(φ)=q and canonical q-scale function W of an unbounded-variation spectrally negative Lévy process give a nondecreasing Esscher tilt V(x)=exp(-φx)W(x) bounded above uniformly for x>0. The first part comes from the first-passage ratio inequality and uniqueness of the positive root. For the bound, combine the shifted scale Laplace identity with convexity at the positive root, obtaining ψ(φ+θ)-q ≥ cθ for θ>0. For a positive increasing V, integrating exp(-θx)V(x) on the tail x≥1/θ gives V(1/θ)e^-1/θ ≤ 1/(ψ(φ+θ)-q) and hence a uniform constant bound. This isolates the substantial Lévy-exponent and Laplace-integral estimate. Monotone convergence then yields the requested positive finite limit in its parent.
-- source:
--   Kuznetsov, Kyprianou and Rivero (2013), The Theory of Scale Functions for Spectrally Negative Lévy Processes; tilted scale-function Laplace transform and positive-root derivative. Reuses Proved esscher_tilted_scale_laplace_shift and convex_positive_root_derivative_pos.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.unbounded_esscher_tilted_scale_monotone_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    MonotoneOn V (Ioi (0 : ℝ)) ∧
      ∃ C : ℝ, ∀ x : ℝ, 0 < x → V x ≤ C := by sorry
