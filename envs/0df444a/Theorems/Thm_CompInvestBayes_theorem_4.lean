-- Prove2me | Theorems.Thm_CompInvestBayes_theorem_4
-- name    : CompInvestBayes.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:08:31.223339+00:00
-- url     : https://prove2.me/theorems/4a1ff062-1fb8-4e4a-93e3-f2f6b627097e
-- title:
--   Theorem 4 (corrected: requires $c_1\le c_2$) — for large $\sigma$ the leader's equilibrium value strictly decreases in the prior near $c_2\lambda$
-- statement:
--   Let the standing assumptions hold and $c_1\le c_2$, and suppose the three conditions (30)
--
--   $$
--   \text{(i) } \mu_H-\mu_L<\delta_1:=\frac{\mu_{2,L}(1-2c_2\lambda)}{2c_2\lambda},\qquad
--   \text{(ii) } c_2<\delta_2:=\frac1{2\lambda},\qquad
--   \text{(iii) } \mu_{1,L}<\delta_3:=\mu_{1,H}-\mu_{2,L}.
--   $$
--
--   Then there is $\bar\sigma>0$ such that for every volatility $\sigma>\bar\sigma$ there is a belief region $B=(c_2\lambda-\varepsilon,c_2\lambda+\varepsilon)\subseteq(0,1)$, $\varepsilon>0$, with the following property on every probability space of the model:
--
--   1. the follower has a best response to every leader size $S_1\ge0$ and every prior $y_0\in[0,1]$;
--   2. for every selection of follower best responses, the leader's equilibrium value function $V_1(y_0)=\max_{S_1\ge0}H(S_1,y_0)$ is differentiable at every $y_0\in B$ with
--   $$
--   V_1'(y_0)<0.
--   $$
--
--   In this regime a more optimistic prior hurts the leader: it must invest more to delay the follower's entry, and the extra investment costs more than the delay is worth.
--
--   The printed theorem has no condition relating $c_1$ and $c_2$, and it is false without one. With $\lambda=0.1$, $c_1=5$, $c_2=1$, $\mu_{1,L}=0.5$, $\mu_{1,H}=2$, $\mu_{2,L}=1$, $\mu_{2,H}=2$ (all standing assumptions and (30) hold, $c_2\lambda=0.1$), the size $S_1=\mu_{1,L}$ gives the leader $2.5$ for $y_0\in(0.05,0.15)$, while every $S_1>\mu_L$ gives at most $H_0(S_1,y_0)\le-1$ plus a pre-entry gain that tends to $0$ as $\sigma\to\infty$ (Proposition 3(a)). So for large $\sigma$, $V_1\equiv2.5$ near $c_2\lambda$ and $V_1'(c_2\lambda)=0$. The paper's proof uses $\tilde S_1(c_2\lambda)>\mu_L$ (Step C), which needs $c_1\le c_2$.
--
--   Differences from the source:
--   - correction: no hypothesis relating c₁ and c₂ → adds c₁ ≤ c₂; reason: counterexample λ = 0.1, c₁ = 5, c₂ = 1, µ_{1,L} = 0.5, µ_{1,H} = 2, µ_{2,L} = 1, µ_{2,H} = 2: every assumption and (30) hold, yet V₁ ≡ 2.5 near c₂λ for all large σ, so V₁'(c₂λ) = 0
--   - reading: 'there exist constants δ₁, δ₂ and δ₃' → δ₁ = µ_{2,L}(1 − 2c₂λ)/(2c₂λ), δ₂ = 1/(2λ), δ₃ = µ_{1,H} − µ_{2,L}; reason: the δs of the proof (p.ec24, (EC.91), (EC.94)); δs that may depend on everything would make (30) satisfiable vacuously
--   - reading: 'a belief region B' → B = (c₂λ − ε, c₂λ + ε) ⊆ (0, 1) with ε > 0; reason: the proof gives 'a belief region B that contains c₂λ' by continuity
--   - reading: 'V₁(y₀) strictly decreases in y₀, i.e., V₁'(y₀) < 0' → ∃ d < 0, HasDerivAt V₁ d y₀ at every y₀ ∈ B; reason: the 'i.e.' clause is the derivative statement; it implies strict decrease on B
--   - generalization: V₁ for the follower's optimal policy of Proposition 2 → the existence of follower best responses, and V₁ for every best-response selection; reason: the leader's profit depends on the follower only through τ, and the optimal τ is a.s. unique; the existence clause rules out a vacuous 'every selection'
--   - generalization: one fixed probability space (Ω, F, P) → every probability space satisfying the model's assumptions (Setup); reason: the paper's space is one such space, so the statement specializes to it
--   - encoding: max_{S₁≥0} H(S₁, y₀) → sSup over S₁ ≥ 0; reason: Lean convention; payoffs are bounded above by µ_H/λ
--   - encoding: Itô integrals ∫ e^{-λt} dX_t → the pathwise integration-by-parts expression discInt; reason: equal a.s. for the deterministic C¹ integrand e^{-λt}
--   - encoding: a binary θ with P(θ = 1) = π₀ = y₀ → θ := 1{U < y₀} for a uniform U independent of the Brownian motions; reason: puts every prior on one space, so V₁ is a function of y₀
--   - encoding: the natural filtration of X^s_1 with the standard properties → Mathlib's raw natural filtration; reason: the optimal exit time is a stopping time of the raw filtration and (EC.22) bounds every stopping time of either, so the values coincide
--   - reading: 'an investment size S₂ ≥ 0' → an F_τ-measurable random variable S₂ ≥ 0; reason: the optimal size depends on π_τ (Proposition 2); a size that may depend on the future is not a strategy
-- source:
--   Sunar, Yu, Kulkarni, Competitive Investment with Bayesian Learning: Choice of Business Size and Timing, SSRN 3408260 (submitted version), Theorem 4, eq. (30), p.17 (PDF 17); δ₃ p.ec24, (EC.91) p.ec27, (EC.94) p.ec28 (PDF 56–60)

import Mathlib
import Definitions.Def_CompInvestBayes_V1

open MeasureTheory ProbabilityTheory
open scoped NNReal

universe u

namespace CompInvestBayes

/-- **Theorem 4** (SSRN 3408260, p.17, PDF 17), corrected by the hypothesis `c₁ ≤ c₂`, with the
constants `δ₁, δ₂, δ₃` of its proof (p.ec24, (EC.91), (EC.94), PDF 56–60).

Under the standing assumptions, `c₁ ≤ c₂`, and the three conditions (30)
(i) `µ_H − µ_L < δ₁ := µ_{2,L}(1 − 2c₂λ)/(2c₂λ)`, (ii) `c₂ < δ₂ := 1/(2λ)`,
(iii) `µ_{1,L} < δ₃ := µ_{1,H} − µ_{2,L}`,
there is `σ̄ > 0` such that for every volatility `σ > σ̄` there is a belief region
`B = (c₂λ − ε, c₂λ + ε) ⊆ (0, 1)` with the following property on every probability space of the
model: the follower has a best response to every leader size `S₁ ≥ 0` and prior `y₀ ∈ [0, 1]`, and
for every selection of follower best responses the leader's equilibrium value function `V₁` has a
strictly negative derivative `V₁'(y₀) < 0` at every `y₀ ∈ B`. -/
theorem theorem_4 (p : Params) (hp : p.Standing)
    (h_i : p.muH - p.muL < p.mu2L * (1 - 2 * p.c2 * p.lam) / (2 * p.c2 * p.lam))
    (h_ii : p.c2 < 1 / (2 * p.lam))
    (h_iii : p.mu1L < p.mu1H - p.mu2L)
    (hc : p.c1 ≤ p.c2) :
    ∃ σbar : ℝ, 0 < σbar ∧ ∀ σ : ℝ, σbar < σ →
      ∃ ε : ℝ, 0 < ε ∧ 0 < p.c2 * p.lam - ε ∧ p.c2 * p.lam + ε < 1 ∧
        ∀ (Ω : Type u) [MeasurableSpace Ω] (E : Setup Ω),
          (∀ S1 : ℝ, 0 ≤ S1 → ∀ y0 ∈ Set.Icc (0 : ℝ) 1,
              ∃ s : FollowerStrategy p σ E S1 y0, IsFollowerOptimal s) ∧
            ∀ br : (S1 y0 : ℝ) → FollowerStrategy p σ E S1 y0, IsBestResponseSelection br →
              ∀ y ∈ Set.Ioo (p.c2 * p.lam - ε) (p.c2 * p.lam + ε),
                ∃ d : ℝ, d < 0 ∧ HasDerivAt (V1 p σ E br) d y := by sorry

end CompInvestBayes
