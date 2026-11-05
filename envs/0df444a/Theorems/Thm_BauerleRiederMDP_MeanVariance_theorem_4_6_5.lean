-- Prove2me | Theorems.Thm_BauerleRiederMDP_MeanVariance_theorem_4_6_5
-- name    : BauerleRiederMDP.MeanVariance.theorem_4_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:27:11.995297+00:00
-- url     : https://prove2.me/theorems/c9d8d8b5-e330-4710-b4bc-a2bd8a11cf6a
-- title:
--   Theorem 4.6.5 — the auxiliary problem $QP(b)$ has quadratic value functions and a linear optimal policy
-- statement:
--   Consider the $N$-period market of §4.6: a bond with prices $S^0_0=1$, $S^0_{n}=\prod_{k=1}^{n}(1+i_k)$ for deterministic interest rates $i_k$, and $d$ risky assets with independent relative risks $R_1,\dots,R_N\in\mathbb R^d$ satisfying Assumption (FM): $\mathbb E\|R_n\|<\infty$, $\mathbb E R_n\neq 0$, and the covariance matrix of $R_n$ is positive definite, $n=1,\dots,N$. A Markov policy $\pi=(f_0,\dots,f_{N-1})$ invests $f_n(X_n)\in\mathbb R^d$ in the risky assets, and the wealth evolves by $X_{n+1}=(1+i_{n+1})(X_n+f_n(X_n)\cdot R_{n+1})$. For $b\in\mathbb R$, problem $QP(b)$ asks to minimize $\mathbb E^{\pi}_{x_0}[(X_N-b)^2]$ over $\pi\in F^N$. Let $C_n=\mathbb E[R_nR_n^\top]$ and let $(d_n)$ be defined by (4.34). Then:
--
--   1. The value functions are
--   $$V_n(x)=\Big(\frac{xS^0_N}{S^0_n}-b\Big)^2 d_n,\qquad x\in\mathbb R,\ 0\le n\le N,$$
--   and $V_0(x_0)$ is the value of $QP(b)$.
--   2. The policy $\pi^*=(f^*_0,\dots,f^*_{N-1})$ with
--   $$f^*_n(x)=\Big(\frac{bS^0_n}{S^0_N}-x\Big)C_{n+1}^{-1}\,\mathbb E[R_{n+1}],\qquad x\in\mathbb R,$$
--   is optimal: from every initial wealth $x$ its cost equals $V_0(x)$; in particular it solves $QP(b)$ from $x_0$.
--   3. The first and second moments of the terminal wealth under $\pi^*$ are
--   $$\mathbb E^{\pi^*}_{x_0}[X_N]=x_0S^0_Nd_0+b(1-d_0),\qquad \mathbb E^{\pi^*}_{x_0}[X_N^2]=(x_0S^0_N)^2d_0+b^2(1-d_0).$$
--
--   This is the linear-quadratic core of the multiperiod mean-variance problem: by Lemma 4.6.3 every solution of the Lagrange problem $P(\lambda)$ solves some $QP(b)$, and inserting the right $b$ into these formulas gives the efficient frontier of Theorem 4.6.6.
--
--   **Formalization Note** The market is the platform structure `MVMarket` (fields: probability space, interest rates, independent relative risks, Assumption (FM), initial wealth $x_0>0$, benchmark $\mu$ with $x_0S^0_N<\mu$). Policies are maps $\mathbb N\to\mathbb R\to\mathbb R^d$, of which only the rules at times $n\le k<N$ matter. Competitors are policies with measurable rules and square-integrable terminal wealth. $C_{n+1}^{-1}$ is the matrix inverse, a true inverse because $C_{n+1}$ is positive definite under (FM)(ii). The optimality clause follows the book's definition of an optimal policy (§2.1, p.18): $V_{0\pi^*}(x)=V_0(x)$ for all $x$.
--
--   Differences from the source:
--   - generalization: deterministic interest rates $i_n\ge 0$ → any deterministic $i_n$ with $1+i_n>0$; reason: only positivity of the bond prices $S^0_n$ enters, and $i_n\ge0$ is a special case
--   - generalization: relative risks $R_n$ with values in $\mathcal Z=[-1,\infty)^d$ → $R_n$ arbitrary measurable $\mathbb R^d$-valued random vectors; reason: the bound $R_n\ge-1$ is not used by the result, and the book's markets are special cases
--   - reading: (FM)(i) $\mathbb E\|R_n\|<\infty$ together with the covariance matrix of (FM)(ii) → every component of $R_n$ square integrable; reason: the covariance matrix in (FM)(ii) and $C_n=\mathbb E[R_nR_n^\top]$ exist only for finite second moments, so (FM)(ii) presupposes them
--   - encoding: $\pi\in F^N$, all Markov policies with measurable decision rules → Markov policies with measurable rules and square-integrable terminal wealth; reason: a policy with $\mathbb E[(X_N-b)^2]=\infty$ cannot lower the infimum, so no value changes
--   - encoding: $d_n$ by the backward recursion (4.34) → the closed form $\prod_{k=n+1}^N(1-\ell_k)$; reason: the same numbers for $0\le n\le N$
--   - encoding: $\pi=(f_0,\dots,f_{N-1})$ and $\mathbb E^{\pi}_{nx}$, the expectation under the law of the state process → total maps $\mathbb N\to\mathbb R\to\mathbb R^d$, of which only the rules at times $n\le k<N$ enter; the wealth recursion evaluated pathwise on the probability space $(\Omega,\mathbb P)$ carrying $R_1,\dots,R_N$, with a Bochner integral; reason: rules outside the horizon never enter, and $X_N$ has the same law under both constructions, since $Q^Z_n$ is the distribution of $R_{n+1}$ and the $R_n$ are independent
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 4.6.5, pp.121–122 (PDF pp.135–136)

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket
import Definitions.Def_MDPFinance_MeanVariance_MVAuxiliary
import Definitions.Def_BauerleRiederMDP_MeanVariance_dcoef
import Definitions.Def_BauerleRiederMDP_MeanVariance_qpCost
import Definitions.Def_BauerleRiederMDP_MeanVariance_qpValue

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.MeanVariance

open MDPFinance.MeanVariance

/-- **Theorem 4.6.5** (Bäuerle & Rieder, *Markov Decision Processes with Applications to
Finance* (2011), Theorem 4.6.5, pp.121–122, PDF pp.135–136). For the solution of the Markov
Decision Problem `QP(b)` (minimize `𝔼^π_{x_0}[(X_N - b)^2]` over `π ∈ F^N`) in the market of
§4.6 under Assumption (FM) (carried by `M : MVMarket Ω d`):

a) the value functions are `V_n(x) = (x S⁰_N / S⁰_n - b)^2 d_n` for `x ∈ E`, `0 ≤ n ≤ N`, with
   `(d_n)` from (4.34), and `V_0(x_0)` is the value of `QP(b)`;
b) the policy `π* = (f*_0, …, f*_{N-1})`, `f*_n(x) = (b S⁰_n / S⁰_N - x) C_{n+1}⁻¹ 𝔼 R_{n+1}`, is
   optimal: from every initial wealth `x ∈ E` it is admissible and attains `V_0(x)` (the book's
   definition of an optimal policy, §2.1, p.18, PDF p.33: `V_{0π*}(x) = V_0(x)` for all `x ∈ E`); in particular
   it is optimal for `QP(b)` from `x_0`;
c) `𝔼^{π*}_{x_0}[X_N] = x_0 S⁰_N d_0 + b(1 - d_0)` and
   `𝔼^{π*}_{x_0}[X_N^2] = (x_0 S⁰_N)^2 d_0 + b^2(1 - d_0)`.

**Formalization Note.** Markov policies are maps `ℕ → ℝ → ℝ^d` of which only the rules at
times `n ≤ k < N` matter; competitors range over policies with measurable rules and a
square-integrable terminal wealth (a policy with `𝔼[(X_N - b)^2] = ∞` cannot lower an infimum).
`𝔼` is the Bochner integral on the probability space carrying the independent relative risks.
`C_{n+1}⁻¹` is `Matrix.inv`, which is the true inverse because `C_{n+1}` is positive definite
under (FM)(ii). -/
theorem theorem_4_6_5 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : MVMarket Ω d) (b : ℝ) :
    let fstar : ℕ → ℝ → (Fin d → ℝ) := fun n x =>
      (b * M.S0 n / M.S0 M.N - x) • (M.Cmat (n + 1))⁻¹.mulVec (M.Evec (n + 1))
    (∀ n ≤ M.N, ∀ x : ℝ, qpValue M b n x = (x * M.S0 M.N / M.S0 n - b) ^ 2 * dcoef M n) ∧
      qpValue M b 0 M.x0 = (⨅ π : {π : ℕ → ℝ → (Fin d → ℝ) // M.IsAdmissible 0 π},
        ∫ ω, (M.terminalWealth π.1 M.N 0 M.x0 ω - b) ^ 2 ∂M.measIP) ∧
      (∀ x : ℝ, M.IsAdmissibleFrom 0 x fstar ∧ qpCost M b 0 x fstar = qpValue M b 0 x) ∧
      M.IsOptimalQP b fstar ∧
      M.meanXN fstar = M.x0 * M.S0 M.N * dcoef M 0 + b * (1 - dcoef M 0) ∧
      M.meanXNsq fstar = (M.x0 * M.S0 M.N) ^ 2 * dcoef M 0 + b ^ 2 * (1 - dcoef M 0) := by sorry

end BauerleRiederMDP.MeanVariance
