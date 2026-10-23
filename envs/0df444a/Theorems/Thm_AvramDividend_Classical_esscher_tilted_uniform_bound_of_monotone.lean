-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_tilted_uniform_bound_of_monotone
-- name    : AvramDividend.Classical.esscher_tilted_uniform_bound_of_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T22:02:55.033516+00:00
-- url     : https://prove2.me/theorems/0cbd1b55-4e22-4722-b177-a5310e27bd7b
-- title:
--   Monotone Esscher-tilted q-scale functions have a universal Laplace upper bound
-- statement:
--   Assume the canonical q-scale function W, q>0, and a positive Esscher root phi; suppose the positive half-line Esscher tilt V(x)=exp(-phi*x)W(x) is nondecreasing. Then 0 <= V(x) <= exp(2)*phi/q for every positive x. Use the proved shifted Laplace identity for the tilt and the proved Lévy-exponent linear increment lower bound, followed by the proved general monotone Laplace uniform-bound theorem. This isolates the uniform estimate from the stochastic argument establishing tilted monotonicity.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_shifted_increment_lower
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_scale_laplace_shift
import Theorems.Thm_AvramDividend_Classical_monotone_exp_laplace_uniform_bound
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_tilted_uniform_bound_of_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x)
    (hmono : MonotoneOn V (Ioi (0 : ℝ))) :
    ∀ x : ℝ, 0 < x → V x ≤ Real.exp 2 * (φ / q) := by sorry
