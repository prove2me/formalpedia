-- Prove2me | Theorems.Thm_FollowCustomers_SmallCost_proposition_2
-- name    : FollowCustomers.SmallCost.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:21:16.829172+00:00
-- url     : https://prove2.me/theorems/35379f2d-e930-45e5-bb87-c8673c1514f8
-- title:
--   Proposition 2, p. 14 (PDF 16) — as K → 0 the thresholds rise infinitely fast, increase in σ², decrease in δ, their gap increases in σ² and δ, and r's effect vanishes
-- statement:
--   In the repositioning duopoly with discount rate $r>0$, preference variance $\sigma^2>0$ and attribute weight $\delta>0$, consider solution branches $K\mapsto(\underline x(K),x^*(K))$ of the threshold system (14)–(15): for every sufficiently small repositioning cost $K>0$, the pair solves (14)–(15) in the region $\tfrac12<\underline x<x^*<1$, $\delta(2x^*-1)<3$. Then:
--
--   1. **Infinitely fast increase.** On every branch,
--   $$\frac{x^*(K)-\tfrac12}{K}\to+\infty,\qquad \frac{\underline x(K)-\tfrac12}{K}\to+\infty\qquad(K\to0^+).$$
--   2. **Effect of $\sigma^2$.** If two parameter tuples share $r$ and $\delta$ and have $\sigma_1^2<\sigma_2^2$, then for any branches of the two systems and all sufficiently small $K>0$,
--   $$x_1^*<x_2^*,\qquad \underline x_1<\underline x_2,\qquad x_1^*-\underline x_1<x_2^*-\underline x_2 .$$
--   3. **Effect of $\delta$.** If two tuples share $r$ and $\sigma^2$ and have $\delta_1<\delta_2$, then for any branches and all sufficiently small $K>0$,
--   $$x_2^*<x_1^*,\qquad \underline x_2<\underline x_1,\qquad x_1^*-\underline x_1<x_2^*-\underline x_2 .$$
--   4. **Vanishing effect of $r$.** If two tuples share $\sigma^2$ and $\delta$ (with arbitrary $r_1,r_2$), then for any branches,
--   $$\frac{x_1^*(K)-x_2^*(K)}{x_1^*(K)-\tfrac12}\to0,\qquad \frac{\underline x_1(K)-\underline x_2(K)}{\underline x_1(K)-\tfrac12}\to0\qquad(K\to0^+).$$
--
--   This is Proposition 2 of Ning and Villas-Boas. Higher volatility of consumer tastes makes firms slower to reposition and widens the region in which they mix; a more important repositioning attribute makes them faster to reposition but also widens the mixing region; for small repositioning costs, patience no longer matters to first order.
--
--   **Formalization Note.** "Increase infinitely fast with $K$ as $K\to0$" is read as divergence of the chord slope from the limit value $1/2$, since no differentiability of a branch in $K$ is established. "For a small $K$" means "for all sufficiently small $K>0$", for each fixed pair of parameter tuples. Comparative statics compare two parameter tuples differing in one parameter, each with its own branch. "The effect of the discount rate $r$ approaches zero" is read relative to the displacement of the threshold from $1/2$: the absolute difference of two thresholds tends to $0$ trivially, because both thresholds tend to $1/2$. Every clause quantifies over all solution branches; the existence of branches is a separate milestone.
-- source:
--   Ning & Villas-Boas, Following the Customers: Dynamic Competitive Repositioning, SSRN 3695318 (December 2020), p. 14 (PDF 16), Proposition 2

import Mathlib
import Definitions.Def_FollowCustomers_SmallCost_Model
open Filter Topology

namespace FollowCustomers.SmallCost

/-- Proposition 2, p. 14. (a) The thresholds rise infinitely fast in `K` at `K = 0⁺`:
the chord slopes `(x* − 1/2)/K` and `(x̲ − 1/2)/K` diverge. (b) For small `K`, both thresholds
increase with `σ²`, and so does their gap. (c) For small `K`, both thresholds decrease with `δ`
and their gap increases with `δ`. (d) As `K → 0⁺` the effect of `r` on each threshold,
relative to the displacement of the threshold from `1/2`, vanishes. All clauses hold for every
solution branch of (14)–(15). -/
theorem proposition_2 :
    (∀ (P : Params) (xl xs : ℝ → ℝ), P.Standing → IsBranch P xl xs →
      Tendsto (fun K => (xs K - 1 / 2) / K) (𝓝[>] 0) atTop ∧
        Tendsto (fun K => (xl K - 1 / 2) / K) (𝓝[>] 0) atTop) ∧
    (∀ (P₁ P₂ : Params) (xl₁ xs₁ xl₂ xs₂ : ℝ → ℝ), P₁.Standing → P₂.Standing →
      P₁.r = P₂.r → P₁.δ = P₂.δ → P₁.σ2 < P₂.σ2 →
      IsBranch P₁ xl₁ xs₁ → IsBranch P₂ xl₂ xs₂ →
      ∀ᶠ K in 𝓝[>] 0, xs₁ K < xs₂ K ∧ xl₁ K < xl₂ K ∧ xs₁ K - xl₁ K < xs₂ K - xl₂ K) ∧
    (∀ (P₁ P₂ : Params) (xl₁ xs₁ xl₂ xs₂ : ℝ → ℝ), P₁.Standing → P₂.Standing →
      P₁.r = P₂.r → P₁.σ2 = P₂.σ2 → P₁.δ < P₂.δ →
      IsBranch P₁ xl₁ xs₁ → IsBranch P₂ xl₂ xs₂ →
      ∀ᶠ K in 𝓝[>] 0, xs₂ K < xs₁ K ∧ xl₂ K < xl₁ K ∧ xs₁ K - xl₁ K < xs₂ K - xl₂ K) ∧
    (∀ (P₁ P₂ : Params) (xl₁ xs₁ xl₂ xs₂ : ℝ → ℝ), P₁.Standing → P₂.Standing →
      P₁.σ2 = P₂.σ2 → P₁.δ = P₂.δ →
      IsBranch P₁ xl₁ xs₁ → IsBranch P₂ xl₂ xs₂ →
      Tendsto (fun K => (xs₁ K - xs₂ K) / (xs₁ K - 1 / 2)) (𝓝[>] 0) (𝓝 0) ∧
        Tendsto (fun K => (xl₁ K - xl₂ K) / (xl₁ K - 1 / 2)) (𝓝[>] 0) (𝓝 0)) := by sorry

end FollowCustomers.SmallCost
