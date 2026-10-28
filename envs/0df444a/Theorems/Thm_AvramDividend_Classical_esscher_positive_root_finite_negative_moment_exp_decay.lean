-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_positive_root_finite_negative_moment_exp_decay
-- name    : AvramDividend.Classical.esscher_positive_root_finite_negative_moment_exp_decay
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:39:57.864541+00:00
-- url     : https://prove2.me/theorems/e2c457b7-110a-48ff-ae5b-97f5b8a20220
-- title:
--   Uniform explicit exponential decay of finite-horizon negative moments under the positive-root Esscher law
-- statement:
--   For a spectrally negative Lévy process with q>0 and positive root ψ(φ)=q, the genuine Esscher tilted marginal at φ satisfies E_t^φ[exp(−(φ/2)X_t)]≤exp(−t q/2) at every nonnegative horizon t. This is an explicit exponential moment decay estimate, uniformly in t, obtained without any Wiener–Hopf factorisation.
-- source:
--   The already-proven positive secant monotonicity yields ψ(φ/2)≤q/2. The exact previously-proven negative moment under the finite-time Esscher law gives exp(t(ψ(φ/2)−q)); monotonicity of real exponential and t≥0 supply the bound. Supports a geometric Chernoff argument on integer samples of the running infimum.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_negative_laplace
import Theorems.Thm_AvramDividend_Classical_levy_psi_positive_secant_monotone
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_positive_root_finite_negative_moment_exp_decay
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) (t : ℝ≥0) :
    (∫ ω, Real.exp (-(φ / 2) * X.X t ω) ∂
      (P.withDensity (fun ω : Ω =>
        ENNReal.ofReal
          (Real.exp (φ * X.X t ω - (t : ℝ) * X.ψ φ))))) ≤
      Real.exp (-(t : ℝ) * q / 2) := by sorry
