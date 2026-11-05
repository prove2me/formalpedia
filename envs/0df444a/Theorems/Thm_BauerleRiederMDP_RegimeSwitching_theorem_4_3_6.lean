-- Prove2me | Theorems.Thm_BauerleRiederMDP_RegimeSwitching_theorem_4_3_6
-- name    : BauerleRiederMDP.RegimeSwitching.theorem_4_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:27:54.055778+00:00
-- url     : https://prove2.me/theorems/d2104a51-ed50-448d-82e6-a39bfe285395
-- title:
--   Theorem 4.3.6 — power-utility consumption-investment: $V_n(x)=d_nx^\gamma$ and the optimal policy
-- statement:
--   In the multiperiod consumption-investment problem of §4.3, let the interest rates be $i_n\ge0$, the relative risks $R_1,\dots,R_N$ independent with $R_n>-1$ a.s., and let Assumption (FM) hold: no arbitrage and $\mathbb E\|R_n\|<\infty$ for $n=1,\dots,N$. Let $U_c(x)=U_p(x)=\frac1\gamma x^\gamma$ on $[0,\infty)$ with $0<\gamma<1$, and $\delta=(1-\gamma)^{-1}$.
--
--   1. The value functions are
--   $$V_n(x)=d_nx^\gamma,\qquad x\ge0,$$
--   where $d_N=\frac1\gamma$ and $d_n^\delta=\gamma^{-\delta}+\big((1+i_{n+1})^\gamma v_n\big)^\delta d_{n+1}^\delta$, with $v_n$ the value of problem (4.7).
--   2. Problem (4.7) has an optimal solution $\alpha_n^*$ for each $n<N$, and for any such choice the policy $(f_0^*,\dots,f_{N-1}^*)$, $f_n^*=(c_n^*,a_n^*)$ with
--   $$c_n^*(x)=x(\gamma d_n)^{-\delta},\qquad a_n^*(x)=x\,\frac{(\gamma d_n)^\delta-1}{(\gamma d_n)^\delta}\,\alpha_n^*,$$
--   is admissible and optimal for the $N$-stage problem.
--
--   The optimal consumption and investment are proportional to wealth, and the investment fractions of the remaining wealth are those of the problem without consumption.
--
--   Differences from the source:
--   - encoding: value functions as suprema of 𝔼^π over policies in the Markov Decision Model → valueFunction of a DisturbanceMDM: supremum over admissible measurable Markov policies of the EReal expectation under the Ionescu–Tulcea path measure; reason: the book's definition (pp.16–18); Markov policies suffice by Theorem 2.2.3
--   - encoding: state space [0, ∞), next wealth (1 + i)(x − c + a·z) → state space ℝ≥0 with next wealth Real.toNNReal((1 + i)(x − c + a·z)); reason: for admissible actions the wealth is ≥ 0 a.s., so the truncation changes no law; it keeps T inside the state space for every z
--   - encoding: Assumption (FM)(i): no arbitrage in the N-period market with independent R_n → NoArbitrageLaw (μ n) for the law of each R_n, n = 1, …, N; reason: equivalent by Theorem 3.1.5 (local form) for independent relative risks; the model uses only the laws (Q^Z_n = law of R_{n+1})
--   - reading: α*_n is the optimal solution of problem (4.7) → (4.7) has an optimal solution, and the conclusion holds for every choice of optimal solutions α*_n; reason: with redundant assets the optimal solution need not be unique; the book's argument works for each
--   - encoding: the optimal consumption is c*_n(x) and the optimal amounts are a*_n(x); the strategy (f*_0, …, f*_{N−1}) is optimal → a Markov policy with these rules exists, is admissible, and has V_{0π} = V_0; reason: the book's notion of an optimal policy (p.18); the formulas are the decision rules
--   - encoding: (d_n) satisfy the recursion → d_n = dCI i μ γ N n, the positive root of the recursion; reason: the recursion determines d_n > 0 uniquely
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 4.3.6, p.97 (PDF p.111); problem (4.7), p.83 (PDF p.97); model p.94 (PDF p.108)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_NoArbitrageLaw
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_valueFunction
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_ciModel
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_dCI
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BauerleRiederMDP.RegimeSwitching

/-- **Theorem 4.3.6** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), p.97, PDF p.111). In the multiperiod consumption-investment problem
of §4.3 with interest rates `i_n ≥ 0`, independent relative risks `R_1, …, R_N` of laws
`μ 1, …, μ N` with `R_n > −1` a.s., Assumption (FM) (no arbitrage, `𝔼‖R_n‖ < ∞`) and power
utilities `U_c(x) = U_p(x) = x^γ / γ`, `0 < γ < 1`:
a) the value functions are `V_n(x) = d_n x^γ`, `x ≥ 0`, with `d_N = 1/γ` and
`d_n^δ = γ^{-δ} + ((1 + i_{n+1})^γ v_n)^δ d_{n+1}^δ`, `δ = (1 − γ)^{-1}`, `v_n` the value of (4.7);
b) problem (4.7) has an optimal solution `α*_n`, and for any choice of optimal solutions the
policy `f*_n = (c*_n, a*_n)` with `c*_n(x) = x (γ d_n)^{-δ}` and
`a*_n(x) = x ((γ d_n)^δ − 1)/(γ d_n)^δ · α*_n` is admissible and optimal for the `N`-stage
problem.

**Formalization Note.** `V_n = valueFunction (ciModel i μ U_c) U_p N n` (Markov policies,
values in `EReal`); `d_n = dCI i μ γ N n`. Optimality is the book's (p.18): `V_{0π} = V_0`.
The power utilities are passed as `c ↦ c^γ / γ` (`Real.rpow`), evaluated only at nonnegative
arguments on the paths of admissible policies. -/
theorem theorem_4_3_6 {d : ℕ} (N : ℕ) (i : ℕ → ℝ) (hi : ∀ n, 1 ≤ n → n ≤ N → 0 ≤ i n)
    (μ : ℕ → ProbabilityMeasure (Fin d → ℝ))
    (hR : ∀ n, 1 ≤ n → n ≤ N → ∀ᵐ z ∂(μ n : Measure (Fin d → ℝ)), ∀ k, -1 < z k)
    (hNA : ∀ n, 1 ≤ n → n ≤ N → NoArbitrageLaw (μ n : Measure (Fin d → ℝ)))
    (hint : ∀ n, 1 ≤ n → n ≤ N →
      Integrable (fun z : Fin d → ℝ => ∑ k, |z k|) (μ n : Measure (Fin d → ℝ)))
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    (∀ n ≤ N, ∀ x : ℝ≥0,
      valueFunction (ciModel i μ (fun c => c ^ γ / γ)) (fun x => (x : ℝ) ^ γ / γ) N n x =
        ((dCI i μ γ N n * (x : ℝ) ^ γ : ℝ) : EReal)) ∧
    (∀ n < N, ∃ α ∈ admFrac (μ (n + 1) : Measure (Fin d → ℝ)),
      ∫⁻ z, ENNReal.ofReal ((1 + ∑ k, α k * z k) ^ γ) ∂(μ (n + 1) : Measure (Fin d → ℝ)) =
        powerValue (μ (n + 1) : Measure (Fin d → ℝ)) γ) ∧
    ∀ αstar : ℕ → Fin d → ℝ, (∀ n < N, αstar n ∈ admFrac (μ (n + 1) : Measure (Fin d → ℝ)) ∧
        ∫⁻ z, ENNReal.ofReal ((1 + ∑ k, αstar n k * z k) ^ γ) ∂(μ (n + 1) : Measure (Fin d → ℝ)) =
          powerValue (μ (n + 1) : Measure (Fin d → ℝ)) γ) →
      ∃ π : MarkovPolicy ℝ≥0 (ℝ × (Fin d → ℝ)),
        (∀ n < N, ∀ x : ℝ≥0, π.f n x =
          ((x : ℝ) * (γ * dCI i μ γ N n) ^ (-(1 - γ)⁻¹),
            fun k => (x : ℝ) * (((γ * dCI i μ γ N n) ^ (1 - γ)⁻¹ - 1) /
              (γ * dCI i μ γ N n) ^ (1 - γ)⁻¹) * αstar n k)) ∧
        π.IsAdmissible (ciModel i μ (fun c => c ^ γ / γ)) 0 N ∧
        ∀ x : ℝ≥0,
          policyValue (ciModel i μ (fun c => c ^ γ / γ)) (fun x => (x : ℝ) ^ γ / γ) N π 0 x =
            valueFunction (ciModel i μ (fun c => c ^ γ / γ))
              (fun x => (x : ℝ) ^ γ / γ) N 0 x := by sorry

end BauerleRiederMDP.RegimeSwitching
