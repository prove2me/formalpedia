-- Prove2me | Theorems.Thm_BauerleRiederMDP_PartialObs_theorem_6_2_3
-- name    : BauerleRiederMDP.PartialObs.theorem_6_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:05:27.99141+00:00
-- url     : https://prove2.me/theorems/53637c09-53c5-40e6-a02d-d72086eeb435
-- title:
--   Theorem 6.2.3 — the mean-variance problem under partial observation
-- statement:
--   Consider the dynamic mean–variance problem with partial observation of Section 6.2: a bond with rates $i_n\ge0$ and price $S^0_n$, $d$ stocks whose relative risk depends on a hidden Markov chain with prior $Q_0$, wealth $E_X=\mathbb R$, unconstrained investments, horizon $N\ge1$, initial wealth $x_0$ and target $\mu$, under Assumption (FM): (i) $\sup_y\mathbb E\|R(y)\|^2<\infty$, (ii) some coordinate of $\mathbb E R(y)$ has a strict sign independent of $y$, (iii) $\operatorname{Cov}(R(y))$ is positive definite for all $y$, (iv) $x_0S^0_N<\mu$. Let $d_n$, $\ell_n$, $C_n$ be given by (6.7), and for $(x,\rho)\in\mathbb R\times\mathbb P(E_Y)$ let
--   $$
--   f^*_n(x,\rho)=\Big(\frac{\mu-d_0(Q_0)x_0S^0_N}{1-d_0(Q_0)}\,\frac{S^0_n}{S^0_N}-x\Big)\,C^{-1}_{n+1}(\rho)\,\ell_{n+1}(\rho),
--   $$
--   and let $\pi^*=(f_0,\dots,f_{N-1})$ with $f_n(h_n):=f^*_n\big(x_n,\mu_n(\cdot\mid h_n)\big)$, $\mu_n$ the filter. Then:
--
--   1. $\pi^*$ is admissible for (MV) and $\mathbb E^{\pi^*}_{x_0}[X_N]=\mu$;
--   2. $$\operatorname{Var}^{\pi^*}_{x_0}[X_N]=\frac{d_0(Q_0)}{1-d_0(Q_0)}\Big(\mathbb E^{\pi^*}_{x_0}[X_N]-x_0S^0_N\Big)^2;$$
--   3. this variance is the value of (MV), i.e. $\pi^*$ is optimal for (MV).
--
--   The optimal strategy invests, in each period, a multiple of $C^{-1}_{n+1}\ell_{n+1}$ evaluated at the current filter, proportional to the gap between a discounted target and the current wealth.
--
--   Differences from the source:
--   - reading: (FM)(i) $\sup_y\mathbb E\|R(y)\|<\infty$ → $\sup_y\mathbb E\|R(y)\|^2<\infty$; reason: the covariance matrices of (FM)(iii) and the matrices $C_n(\rho)$ of (6.7), used for every $\rho\in\mathbb P(E_Y)$, require finite second moments under every mixture $\int Q^R(\cdot\mid y)\rho(dy)$, and for all $\rho$ at once this is exactly the uniform second-moment bound (which implies the first-moment bound): if $\mathbb E\|R(y_k)\|^2\ge4^k$, the belief $\rho=\sum_k2^{-k}\delta_{y_k}$ makes $C_n(\rho)$ infinite, against the book's "real-valued functions $d_n(\rho)$" (p.185)
--   - encoding: $\pi\in\Pi_N$ in (MV) → measurable functions of the observed returns whose terminal wealth is square integrable; reason: the observable history is a function of $x_0$, the strategy and the returns; other strategies have infinite variance or no mean and do not change the infimum
--   - encoding: horizon $N\in\mathbb N$ → $N\ge1$; reason: the book's $\mathbb N$ starts at $1$, and (6.7) and Lemma 6.2.1 concern $n=0,\dots,N-1$
--   - encoding: $d_n$, $\ell_{n+1}$, $C_{n+1}$ for horizon $N$ → the sequence indexed by stages to go, evaluated at $N-n$ and $N-(n+1)$; reason: same functions
--   - encoding: "The value of (MV) is given by … ; π* is optimal" → four conjuncts (admissibility, mean $=\mu$, variance formula, variance $=$ value); reason: the theorem's parts a) and b) restated
--   - encoding: Bayes operator undefined where its normalizing constant is $0$ or $\infty$ → defined as $\rho$ there; reason: a null set of $z$ under the predictive law, so no integral changes
--   - encoding: $C_{n+1}(\rho)^{-1}$ → Mathlib's matrix inverse; reason: the two agree because $C_{n+1}(\rho)$ is positive definite under (FM)
--   - encoding: $E_Y$ a Borel subset of a Polish space → $E_Y$ a standard Borel space; reason: the two classes coincide up to isomorphism
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 6.2.3, p.188 (PDF 201); setting and Assumption (FM) §6.2, p.184 (PDF 197); (6.7), p.185 (PDF 198)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_FM62
import Definitions.Def_BauerleRiederMDP_PartialObs_S0
import Definitions.Def_BauerleRiederMDP_PartialObs_dSeq
import Definitions.Def_BauerleRiederMDP_PartialObs_mvValue
import Definitions.Def_BauerleRiederMDP_PartialObs_markovStrategy

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **Theorem 6.2.3** (mean-variance problem with partial observation).
Bäuerle & Rieder (2011), Theorem 6.2.3, p.188 (PDF 201): "For the mean-variance problem (MV) with
partial observation it holds:
a) The value of (MV) is given by
`Var^{π*}_{x_0}[X_N] = d_0(Q_0)/(1 − d_0(Q_0)) (IE^{π*}_{x_0}[X_N] − x_0 S^0_N)²`
where `d_0(Q_0)` is given in (6.7). Note that `IE^{π*}_{x_0}[X_N] = μ`.
b) For `(x, ρ) ∈ E_X × IP(E_Y)` let
`f*_n(x, ρ) = (((μ − d_0(Q_0) x_0 S^0_N)/(1 − d_0(Q_0))) S^0_n/S^0_N − x) C^{−1}_{n+1}(ρ) ℓ_{n+1}(ρ)`.
Then the portfolio strategy `π* = (f_0, …, f_{N−1})` is optimal for (MV) where
`f_n(h_n) := f*_n(x_n, μ_n(·|h_n))`, `h_n = (x_0, z_1, x_1, …, z_n, x_n)`."
Setting of §6.2, p.184 (PDF 197): `E_X = ℝ`, `A = ℝ^d`, `D_n(x) = A`, interest rates `i_n ≥ 0`,
`T_{n,X}(x, a, z) = (1 + i_{n+1})(x + a · z)`, and Assumption (FM) (i)–(iv).

**Formalization Note.** `d_n`, `ℓ_n`, `C_n` of (6.7) for horizon `N` are `dSeq M (N − n)` and
`ell`/`Cmat` applied to it; `C^{−1}` is Mathlib's matrix inverse. The horizon is `N ≥ 1`. The
conclusion lists: `π*` is admissible for (MV) (measurable, `X_N ∈ L²`, `IE X_N ≥ μ`);
`IE^{π*} X_N = μ`; the variance formula; and `Var^{π*} X_N` equals the value of (MV), i.e. `π*` is
optimal. (FM)(i) is used in its `L²` form (see `FM62`). -/
theorem theorem_6_2_3 {EY : Type*} [MeasurableSpace EY] [StandardBorelSpace EY] {d : ℕ}
    (M : Market EY d) (i : ℕ → ℝ) (hi : ∀ n, 0 ≤ i n) (hFM : FM62 M) (N : ℕ) (hN : 1 ≤ N)
    (x0 μ : ℝ) (hμ : x0 * S0 i N < μ) :
    let d0 : ℝ := dSeq M N M.Q0
    let fstar : ℕ → ℝ × ProbabilityMeasure EY → Fin d → ℝ := fun n p =>
      ((μ - d0 * x0 * S0 i N) / (1 - d0) * (S0 i n / S0 i N) - p.1) •
        ((Cmat M (dSeq M (N - (n + 1))) p.2)⁻¹ *ᵥ ell M (dSeq M (N - (n + 1))) p.2)
    let πstar := markovStrategy M i x0 M.Q0 fstar
    let P := M.returnLaw M.Q0 N
    let X := wealth i x0 πstar N
    mvAdmissible M i N x0 μ πstar ∧
      ∫ r, X r ∂P = μ ∧
      ∫ r, (X r - ∫ r', X r' ∂P) ^ 2 ∂P = d0 / (1 - d0) * (∫ r, X r ∂P - x0 * S0 i N) ^ 2 ∧
      ((∫ r, (X r - ∫ r', X r' ∂P) ^ 2 ∂P : ℝ) : EReal) = mvValue M i N x0 μ := by sorry

end BauerleRiederMDP.PartialObs
