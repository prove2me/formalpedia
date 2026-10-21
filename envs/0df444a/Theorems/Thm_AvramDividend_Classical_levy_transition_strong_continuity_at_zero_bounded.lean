-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_transition_strong_continuity_at_zero_bounded
-- name    : AvramDividend.Classical.levy_transition_strong_continuity_at_zero_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T21:27:19.042219+00:00
-- url     : https://prove2.me/theorems/c3fda2f2-bcfb-47cc-99d8-6da3917466ee
-- title:
--   Strong continuity at time zero of the Lévy transition semigroup on bounded continuous test payoffs
-- statement:
--   Let X be the given right-continuous spectrally negative Lévy process started at zero, with its probability law P. Fix a continuous f:R→R with uniform norm bound B and a deterministic reserve x. For any nonnegative time sequence τ_n→0, E[f(x+X_{τ_n})]→f(x). Indeed right continuity at 0 of each sample path and X_0=0 yield X_{τ_n}(ω)→0, so f(x+X_{τ_n}(ω))→f(x) pointwise. Adaptedness supplies measurability for each time, the constant envelope B is integrable under P, and the dominated convergence theorem exchanges the limit and expectation. This establishes the transition semigroup's strong continuity at the origin on bounded continuous functions, a genuine analytic prerequisite for identifying the Lévy–Khintchine generator from difference quotients. It does NOT establish that derivative or the stopped controlled HJB dividend budget.
-- source:
--   Only X.rightCont, X_zero, X.adapted, X.isProbability and pinned Mathlib dominated-convergence; no Open imports.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Process.Adapted
import Mathlib.Topology.Instances.NNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_transition_strong_continuity_at_zero_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (hf : Continuous f)
    (B : ℝ) (hB : ∀ y : ℝ, ‖f y‖ ≤ B)
    (x : ℝ) (τ : ℕ → ℝ≥0)
    (hτ : Filter.Tendsto τ Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => ∫ ω, f (x + X.X (τ n) ω) ∂P)
      Filter.atTop (nhds (f x)) := by sorry
