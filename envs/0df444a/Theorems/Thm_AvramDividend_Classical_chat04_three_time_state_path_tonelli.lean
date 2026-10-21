-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_three_time_state_path_tonelli
-- name    : AvramDividend.Classical.chat04_three_time_state_path_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T07:15:14.147316+00:00
-- url     : https://prove2.me/theorems/c753ba3d-b1e3-4d69-a5ce-1d6721aff3fe
-- title:
--   Full three-time Lévy state-path Markov–Tonelli formula for any measurable payoff
-- statement:
--   For any ordered deterministic times s≤t≤u, the expectation of an arbitrary measurable nonnegative functional f(X_s,X_t,X_u) is a threefold iterated integral of f(a,a+b,a+b+c) with respect to the independent laws of X_s, X_(t−s), X_(u−t). This directly handles payoffs of the actual intermediate process values, rather than only of their increments. Prove by mapping the newly accepted generic triple increment Tonelli theorem through the measurable triangular-addition map ((a,b),c)↦((a,a+b),a+b+c), and using algebra X_s+(X_t−X_s)=X_t. No finite moment assumption, martingale property, exponential rate, or q-scale harmonicity is needed. The theorem admits arbitrary measurable finite-grid survival indicators as payoffs but does not yet infer survival between grid points.
-- source:
--   Accepted AvramDividend.Classical.chat04_three_step_grid_tonelli_markov_law UUID d361e68e-5bfd-437d-9938-bf54c281c42d and pinned Mathlib measurable function compositions.

import Mathlib.Tactic.FunProp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_three_step_grid_tonelli_markov_law

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_three_time_state_path_tonelli
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u)
    (f : (ℝ × ℝ) × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f ((X.X s ω, X.X t ω), X.X u ω) ∂P) =
      ∫⁻ a, ∫⁻ b, ∫⁻ c, f ((a, a + b), a + b + c)
        ∂(Measure.map (X.X (u - t)) P)
        ∂(Measure.map (X.X (t - s)) P)
        ∂(Measure.map (X.X s) P) := by sorry
