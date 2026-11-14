-- Prove2me | Theorems.Thm_BauerleRiederMDP_MeanVariance_theorem_4_6_6
-- name    : BauerleRiederMDP.MeanVariance.theorem_4_6_6
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:26:29.958282+00:00
-- url     : https://prove2.me/theorems/8a8b2ce5-b4d5-44cc-b54a-af22d5657a5d
-- title:
--   Theorem 4.6.6 — the multiperiod mean-variance problem: value $\frac{d_0}{1-d_0}(\mu-x_0S^0_N)^2$ and explicit optimal portfolio
-- statement:
--   Consider the $N$-period market of §4.6 ($N\ge1$): a bond with prices $S^0_0=1$, $S^0_n=\prod_{k=1}^n(1+i_k)$, and $d$ risky assets with independent relative risks $R_1,\dots,R_N\in\mathbb R^d$. An investor with initial wealth $x_0>0$ follows a Markov portfolio strategy $\pi=(f_0,\dots,f_{N-1})$, investing $f_n(X_n)\in\mathbb R^d$ in the risky assets, so that $X_{n+1}=(1+i_{n+1})(X_n+f_n(X_n)\cdot R_{n+1})$. Assume (FM): $\mathbb E\|R_n\|<\infty$ and $\mathbb E R_n\neq0$; the covariance matrix of $R_n$ is positive definite ($n=1,\dots,N$); and $x_0S^0_N<\mu$. The mean-variance problem is
--
--   $$(MV)\qquad \operatorname{Var}^{\pi}_{x_0}[X_N]\to\min,\qquad \mathbb E^{\pi}_{x_0}[X_N]\ge\mu,\qquad \pi\in F^N.$$
--
--   Let $C_n=\mathbb E[R_nR_n^\top]$ and let $d_0$ be given by (4.34). Then:
--
--   1. The strategy $\pi^*=(f^*_0,\dots,f^*_{N-1})$ with
--   $$f^*_n(x)=\Big(\frac{\mu-d_0x_0S^0_N}{1-d_0}\cdot\frac{S^0_n}{S^0_N}-x\Big)C_{n+1}^{-1}\,\mathbb E[R_{n+1}],\qquad x\in\mathbb R,$$
--   is optimal for (MV): it satisfies the constraint and has the smallest variance among all strategies that do.
--   2. $\mathbb E^{\pi^*}_{x_0}[X_N]=\mu$, and the value of (MV) is
--   $$\operatorname{Var}^{\pi^*}_{x_0}[X_N]=\frac{d_0}{1-d_0}\Big(\mathbb E^{\pi^*}_{x_0}[X_N]-x_0S^0_N\Big)^2,$$
--   which equals the infimum of $\operatorname{Var}^{\pi}_{x_0}[X_N]$ over all feasible $\pi$.
--
--   Equivalently, the efficient frontier is the line $\mu=x_0S^0_N+\sigma\sqrt{(1-d_0)/d_0}$ in the (standard deviation, mean) plane, and at every time the optimal strategy splits the money between the bond and one mutual fund with direction $C_{n+1}^{-1}\mathbb E[R_{n+1}]$.
--
--   **Formalization Note** The market is the platform structure `MVMarket`. Strategies are maps $\mathbb N\to\mathbb R\to\mathbb R^d$ with measurable rules and square-integrable terminal wealth (`IsAdmissible`), so that mean and variance exist; the variance is $\mathbb E[X_N^2]-(\mathbb E X_N)^2$ with Bochner integrals. Optimality (`IsOptimalMV`) quantifies over all such feasible strategies, and the value is stated as an infimum over the feasible ones. $C_{n+1}^{-1}$ is the matrix inverse, a true inverse under (FM)(ii).
--
--   Differences from the source:
--   - generalization: deterministic interest rates $i_n\ge 0$ → any deterministic $i_n$ with $1+i_n>0$; reason: only positivity of the bond prices $S^0_n$ enters, and $i_n\ge0$ is a special case
--   - generalization: relative risks $R_n$ with values in $\mathcal Z=[-1,\infty)^d$ → $R_n$ arbitrary measurable $\mathbb R^d$-valued random vectors; reason: the bound $R_n\ge-1$ is not used by the result, and the book's markets are special cases
--   - reading: (FM)(i) $\mathbb E\|R_n\|<\infty$ together with the covariance matrix of (FM)(ii) → every component of $R_n$ square integrable; reason: the covariance matrix in (FM)(ii) and $C_n=\mathbb E[R_nR_n^\top]$ exist only for finite second moments, so (FM)(ii) presupposes them
--   - encoding: $\pi\in F^N$, all Markov strategies with measurable decision rules → Markov strategies with measurable rules and square-integrable terminal wealth; reason: a strategy whose terminal wealth is not square integrable has infinite or undefined variance and cannot be optimal, so neither the optimum nor the value changes
--   - encoding: $d_0$ by the backward recursion (4.34) → the closed form $\prod_{k=1}^N(1-\ell_k)$; reason: the same number
--   - encoding: an $N$-period market → $N\ge1$; reason: for $N=0$ the book's $d_0=1$ makes $d_0/(1-d_0)$ undefined and (FM)(iii) makes (MV) infeasible; Lemma 4.6.4 ($0<d_0<1$), used in the book's derivation, presupposes $N\ge1$
--   - encoding: $\pi=(f_0,\dots,f_{N-1})$, $\mathbb E^{\pi}_{x_0}$ and $\operatorname{Var}^{\pi}_{x_0}$, under the law of the state process → total maps $\mathbb N\to\mathbb R\to\mathbb R^d$, of which only the rules at times $k<N$ enter; the wealth recursion evaluated pathwise on the probability space $(\Omega,\mathbb P)$ carrying $R_1,\dots,R_N$, with Bochner integrals and $\operatorname{Var}=\mathbb E[X_N^2]-(\mathbb E X_N)^2$; reason: rules outside the horizon never enter, and $X_N$ has the same law under both constructions, since $Q^Z_n$ is the distribution of $R_{n+1}$ and the $R_n$ are independent
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 4.6.6, p.123 (PDF p.137); problem (MV), p.117 (PDF p.131); Assumption (FM), p.118 (PDF p.132)

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket
import Definitions.Def_MDPFinance_MeanVariance_MVAuxiliary
import Definitions.Def_BauerleRiederMDP_MeanVariance_dcoef

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.MeanVariance

open MDPFinance.MeanVariance

/-- **Theorem 4.6.6** (Bäuerle & Rieder, *Markov Decision Processes with Applications to
Finance* (2011), Theorem 4.6.6, p.123, PDF p.137). For the mean-variance problem
`(MV)`: minimize `Var^π_{x_0}[X_N]` subject to `𝔼^π_{x_0}[X_N] ≥ μ`, `π ∈ F^N`, in the market
of §4.6 under Assumption (FM) (carried by `M : MVMarket Ω d`), with `N ≥ 1` periods:

a) the value of `(MV)` is
   `Var^{π*}_{x_0}[X_N] = d_0/(1 - d_0) · (𝔼^{π*}_{x_0}[X_N] - x_0 S⁰_N)^2`, with `d_0` from
   (4.34), and `𝔼^{π*}_{x_0}[X_N] = μ`;
b) the optimal portfolio strategy is `π* = (f*_0, …, f*_{N-1})`,
   `f*_n(x) = ((μ - d_0 x_0 S⁰_N)/(1 - d_0) · S⁰_n/S⁰_N - x) C_{n+1}⁻¹ 𝔼[R_{n+1}]`, `x ∈ E`.

The Lean statement says: `π*` is optimal for `(MV)` (admissible, feasible, and of variance at
most that of every admissible feasible strategy), its mean is `μ`, its variance is given by the
formula, and the value of `(MV)` (the infimum of the variance over admissible feasible
strategies) equals `Var^{π*}_{x_0}[X_N]`.

**Formalization Note.** `N ≥ 1`: for `N = 0` the book's `d_0 = 1` makes `d_0/(1 - d_0)`
undefined, and (FM)(iii) `x_0 S⁰_N < μ` makes `(MV)` infeasible. Strategies are Markov,
`ℕ → ℝ → ℝ^d`, with measurable rules and a square-integrable terminal wealth
(`MVMarket.IsAdmissible`), so that mean and variance exist; a strategy whose terminal wealth is
not square integrable has infinite (or undefined) variance and cannot be optimal. `Var` is
`𝔼[X_N^2] - 𝔼[X_N]^2` with Bochner integrals. `C_{n+1}⁻¹` is `Matrix.inv`, the true inverse
under (FM)(ii). -/
theorem theorem_4_6_6 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : MVMarket Ω d)
    (hN : 1 ≤ M.N) :
    let πstar : ℕ → ℝ → (Fin d → ℝ) := fun n x =>
      ((M.μ - dcoef M 0 * M.x0 * M.S0 M.N) / (1 - dcoef M 0) * (M.S0 n / M.S0 M.N) - x) •
        (M.Cmat (n + 1))⁻¹.mulVec (M.Evec (n + 1))
    M.IsOptimalMV πstar ∧
      M.meanXN πstar = M.μ ∧
      M.varXN πstar = dcoef M 0 / (1 - dcoef M 0) * (M.meanXN πstar - M.x0 * M.S0 M.N) ^ 2 ∧
      (⨅ π : {π : ℕ → ℝ → (Fin d → ℝ) // M.IsAdmissible 0 π ∧ M.μ ≤ M.meanXN π},
        M.varXN π.1) = M.varXN πstar := by sorry

end BauerleRiederMDP.MeanVariance
