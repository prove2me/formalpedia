-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_deterministic_scale_expectation_tendsto
-- name    : AvramDividend.Classical.chat04_positive_reserve_deterministic_scale_expectation_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:07:18.379046+00:00
-- url     : https://prove2.me/theorems/e89e3760-ce55-412e-8a3b-7027ff914844
-- title:
--   Time-zero expected q-scale continuity along bounded deterministic observation times
-- statement:
--   For any nonnegative discount q and positive initial reserve x, and any bounded deterministic sequence of times tending to zero, the expectation of exp(-q t) W(x+X_t) converges to W(x), provided the Lévy exponent exceeds q at a nonnegative θ. Uses the newly Proved uniform deterministic-horizon L² bound and an already Proved second-moment Vitali convergence lemma. This controls terminal-only q-scale expectation near time zero and supports the whole-history killed q-scale harmonicity input for the strict two-sided exit identity.
-- source:
--   Exact Proved import chain: deterministic horizon L² 19551a5a, positive reserve pathwise convergence 4940fc29, scale Borel measurability 45cbe3b4, uniform second moment expectation convergence bef79c38. Next: full-filter terminal-only expectation and unbounded killed harmonicity a885f0b3, then stopped exit 09663d0d.

import Theorems.Thm_AvramDividend_Classical_chat04_deterministic_horizon_scale_l2_uniform_bound
import Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_discounted_scale_tendsto_initial
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Theorems.Thm_AvramDividend_Classical_nonnegative_integral_tendsto_of_uniform_second_moment
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.chat04_positive_reserve_deterministic_scale_expectation_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ) (hx : 0 < x)
    (N : ℝ≥0) (t : ℕ → ℝ≥0) (htN : ∀ n, t n ≤ N)
    (ht0 : Filter.Tendsto t Filter.atTop (𝓝 0)) :
    Filter.Tendsto
      (fun n => ∫ ω, Real.exp (-(q * (t n : ℝ))) *
        W (x + X.X (t n) ω) ∂P)
      Filter.atTop (𝓝 (W x)) := by sorry
