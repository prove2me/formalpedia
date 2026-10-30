-- Prove2me | Theorems.Thm_DDROCS_theorem_10_cs_sets
-- name    : DDROCS.theorem_10_cs_sets
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:34:31.636346+00:00
-- url     : https://prove2.me/theorems/215d6ddb-3713-4c47-8892-7eef2a1eb236
-- title:
--   Theorem 10: $\mathcal U^{CS}_\epsilon$ simultaneously imply a guarantee, with support function (34) (corrected: thresholds making $\mathcal P^{CS}$ a $1-\alpha$ confidence region, not bootstrapped)
-- statement:
--   Let $\mathbb P^*$ be a probability measure on $\mathbb R^d$ and let $\mathcal S = (\hat u^1,\dots,\hat u^N)$ be $N$ i.i.d. draws from $\mathbb P^*$, with law $\mathbb P^*_{\mathcal S}$ (the $N$-fold product). Let $\alpha, R \in \mathbb R$. To every sample $\mathcal S$ attach a centre $\hat\mu(\mathcal S) \in \mathbb R^d$, a matrix $\hat\Sigma(\mathcal S) \in \mathbb R^{d\times d}$, thresholds $\Gamma_1(\mathcal S) \ge 0$ and $\Gamma_2(\mathcal S)$, and a matrix $C(\mathcal S)$ with
--
--   $$
--   C(\mathcal S)^\top C(\mathcal S) = \hat\Sigma(\mathcal S) + \Gamma_2(\mathcal S)\, I ,
--   $$
--
--   and let $\mathcal P^{CS}(\mathcal S)$ be the Shawe-Taylor–Cristianini region with radius $R$, centre $\hat\mu(\mathcal S)$, matrix $\hat\Sigma(\mathcal S)$ and thresholds $\Gamma_1(\mathcal S), \Gamma_2(\mathcal S)$. For $0<\epsilon<1$ let
--
--   $$
--   \mathcal U^{CS}_\epsilon(\mathcal S) = \Bigl\{\hat\mu(\mathcal S) + y + C(\mathcal S)^\top w : \|y\| \le \Gamma_1(\mathcal S),\ \|w\| \le \sqrt{\tfrac1\epsilon - 1}\Bigr\}.
--   $$
--
--   Assume that $\mathcal P^{CS}$ is a $1-\alpha$ confidence region: $\mathbb P^*_{\mathcal S}\bigl(\mathbb P^* \in \mathcal P^{CS}(\mathcal S)\bigr) \ge 1-\alpha$. Then:
--
--   1. With probability at least $1-\alpha$ with respect to the sampling, the family $\{\mathcal U^{CS}_\epsilon(\mathcal S) : 0<\epsilon<1\}$ simultaneously implies a probabilistic guarantee for $\mathbb P^*$:
--   $$
--   \mathbb P^*_{\mathcal S}\Bigl(\text{for every } 0<\epsilon<1,\ \mathcal U^{CS}_\epsilon(\mathcal S) \text{ implies a probabilistic guarantee for } \mathbb P^* \text{ at level } \epsilon\Bigr) \;\ge\; 1-\alpha .
--   $$
--   2. For every sample $\mathcal S$, every $0<\epsilon<1$ and every $v \in \mathbb R^d$, the support function is the right-hand side of (34):
--   $$
--   \delta^*\bigl(v \mid \mathcal U^{CS}_\epsilon(\mathcal S)\bigr) = \hat\mu(\mathcal S)^\top v + \Gamma_1(\mathcal S)\|v\|_2 + \sqrt{\frac{1-\epsilon}{\epsilon}}\,\sqrt{v^\top\bigl(\hat\Sigma(\mathcal S) + \Gamma_2(\mathcal S) I\bigr)v}.
--   $$
--
--   The theorem turns a mean–covariance confidence region into an explicit uncertainty set, the sum of a ball and an ellipsoid, whose robust counterpart is a second-order cone constraint and which protects every concave constraint at every level $\epsilon$ simultaneously.
--
--   Differences from the source:
--   - correction: thresholds Γ^B_1, Γ^B_2 bootstrapped by Algorithm 1 (p. 9), "(approximately) valid at level 1 − α" (p. 25) → arbitrary thresholds Γ1 S, Γ2 S with the coverage hypothesis hcov: P∗_S(P∗ ∈ P^CS(S)) ≥ 1 − α; reason: with the bootstrapped thresholds the first clause is false: d = 1, P∗ uniform on {−1, 1}, R = 1, N = 2, α = 0.1, ϵ = 1/4; with probability 1/2 the two sample points coincide, every resample equals the sample, both thresholds are 0, U^CS_ϵ = {û¹}, and the concave g(u) = 1 − û¹u is ≤ 0 on it while P∗(g(ũ) ≤ 0) = 1/2 < 3/4, so the probability in clause 1 is at most 1/2 < 0.9; coverage at level 1 − α is the property the proof uses through Theorem 3
--   - generalization: µ̂, Σ̂ the sample mean and covariance → arbitrary functions µ̂(S), Σ̂(S) of the sample; reason: the proof uses no property of the estimators; the sample mean and either sample-covariance convention are instances
--   - generalization: CᵀC = Σ̂ + Γ^B_2 I a Cholesky decomposition → any matrix C(S) with C(S)ᵀC(S) = Σ̂(S) + Γ2(S) I; reason: a Cholesky factor is such a matrix
--   - generalization: 0 < α < 1 (the schema, p. 10) → any real α; reason: the statement for every α contains the paper's case
--   - reading: Θ(R) the Borel probability measures supported on the ball of radius R → probability measures P with P(closed ball of radius R about 0) = 1; reason: a support is closed, and the ball of Theorem 9 is centred at the origin
--   - reading: ‖y‖, ‖w‖ in (35) → Euclidean norms; reason: (34) has ‖v‖2 and the Cauchy–Schwarz argument of the proof is for the Euclidean norm
--   - encoding: for every x∗ and every f(u,x) concave in u (probabilistic guarantee, (2)) → every concave g : ℝ^d → ℝ (ImpliesGuarantee); reason: x∗ is fixed in (2), so only g = f(·,x∗) matters, and every concave g is f(·,x∗) for f(u,x) := g(u)
--   - encoding: threshold Γ^B_1 (a norm bound) → hypothesis 0 ≤ Γ1 S for every sample; reason: every threshold of the paper is a norm bound, hence nonnegative; a negative threshold would make (35) empty
--   - encoding: probability with respect to the sampling → product measure Measure.pi of N copies of P∗ on samples S : Fin N → ℝ^d, applied to the event as an outer measure; reason: for a measurable event this is its probability; hypothesis and conclusion use the same notion
--   - encoding: δ∗(v| U^CS_ϵ) given explicitly by the right-hand side of (34) → IsLUB of {⟪v, u⟫ : u ∈ UCS} at the right-hand side, for every sample, 0 < ε < 1 and v; reason: the least upper bound of the set is the supremum, without Lean's junk value for a real sSup
-- source:
--   Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 10, p. 25 (proof p. ec8 = PDF p. 46)

import Mathlib
import Definitions.Def_DDROCS_SimultaneouslyImplies
import Definitions.Def_DDROCS_PCS
import Definitions.Def_DDROCS_UCS
open MeasureTheory InnerProductSpace Matrix

namespace DDROCS

/-- **Theorem 10 (corrected: thresholds that make `P^CS` a `1 − α` confidence region).**
Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 10, p. 25:
"With probability at least `1 − α` with respect to the sampling, the family
`{U^CS_ϵ : 0 < ϵ < 1}` simultaneously implies a probabilistic guarantee for `P∗`, where
`U^CS_ϵ = { µ̂ + y + Cᵀw : ∃y, w ∈ ℝ^d s.t. ‖y‖ ≤ Γ^B_1, ‖w‖ ≤ √(1/ϵ − 1) }` (35), where
`CᵀC = Σ̂ + Γ^B_2 I` is a cholesky decomposition. Moreover, `δ∗(v| U^CS_ϵ)` is given explicitly by
the right-hand side of Eq. (34) with `(Γ1, Γ2)` replaced by the bootstrapped thresholds
`Γ^B_1, Γ^B_2`." (Proof on p. ec8.)

Clause 1: with probability at least `1 − α` over the sample, the family `{U^CS_ε}` built from the
sample simultaneously implies a probabilistic guarantee for `P∗` (one event for every `0 < ε < 1`).
Clause 2: for every sample, every `0 < ε < 1` and every `v`, `δ∗(v| U^CS_ε)` is the right-hand side
of (34), as a least upper bound.

**Formalization Note.** *Correction.* The printed thresholds are the bootstrapped `Γ^B_1, Γ^B_2`
of Algorithm 1 (p. 9), which the paper calls "(approximately) valid at level `1 − α`" (p. 25);
with them clause 1 is false at finite `N` (`d = 1`, `P∗` uniform on `{−1, 1}`, `R = 1`, `N = 2`,
`α = 0.1`, `ε = 1/4`: with probability `1/2` the two points coincide, every resample equals the
sample, both bootstrapped thresholds are `0`, `U^CS_ε = {û¹}`, and the concave `g(u) = 1 − û¹u` is
`≤ 0` on it while `P∗(g(ũ) ≤ 0) = 1/2 < 3/4`). Here the thresholds `Γ₁ S`, `Γ₂ S` are arbitrary
functions of the sample, subject to the coverage hypothesis `hcov`: `P^CS` built from them is a
`1 − α` confidence region (p. 9), the property the proof (via Theorem 3) uses. The estimators
`μhat S`, `Sigmahat S` are arbitrary functions of the sample (the sample mean and covariance are
instances), and `C S` is any matrix with `(C S)ᵀ C S = Σ̂ + Γ₂ I` (a Cholesky factor is one).
`0 ≤ Γ₁ S` is assumed (a negative threshold empties (35); every threshold of the paper is a norm
bound). The sample is `S : Fin N → ℝ^d` under `Measure.pi (fun _ => Pstar)`, applied to events
as an outer measure. `0 < α < 1`, a bound on `N` and a support assumption on `P∗` are not assumed
(the last is part of the coverage event). `δ∗` is stated as `IsLUB`; `vᵀAv` is
`∑ i, ∑ j, v i * A i j * v j`. -/
theorem theorem_10_cs_sets {d N : ℕ} (Pstar : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure Pstar] (α R : ℝ)
    (μhat : (Fin N → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    (Sigmahat : (Fin N → EuclideanSpace ℝ (Fin d)) → Matrix (Fin d) (Fin d) ℝ)
    (Γ₁ Γ₂ : (Fin N → EuclideanSpace ℝ (Fin d)) → ℝ) (hΓ₁ : ∀ S, 0 ≤ Γ₁ S)
    (C : (Fin N → EuclideanSpace ℝ (Fin d)) → Matrix (Fin d) (Fin d) ℝ)
    (hC : ∀ S, (C S)ᵀ * C S = Sigmahat S + Γ₂ S • (1 : Matrix (Fin d) (Fin d) ℝ))
    (hcov : 1 - α ≤ (Measure.pi (fun _ : Fin N => Pstar)
      {S | Pstar ∈ PCS R (μhat S) (Sigmahat S) (Γ₁ S) (Γ₂ S)}).toReal) :
    1 - α ≤ (Measure.pi (fun _ : Fin N => Pstar)
      {S | SimultaneouslyImplies (fun ε => UCS (μhat S) (Γ₁ S) (C S) ε) Pstar}).toReal ∧
    ∀ S : Fin N → EuclideanSpace ℝ (Fin d), ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ v : EuclideanSpace ℝ (Fin d),
        IsLUB ((fun u => ⟪v, u⟫_ℝ) '' UCS (μhat S) (Γ₁ S) (C S) ε)
          (⟪μhat S, v⟫_ℝ + Γ₁ S * ‖v‖ + Real.sqrt ((1 - ε) / ε) *
            Real.sqrt (∑ i, ∑ j,
              v i * (Sigmahat S + Γ₂ S • (1 : Matrix (Fin d) (Fin d) ℝ)) i j * v j)) := by sorry

end DDROCS
