-- Prove2me | Theorems.Thm_DantzigSelector_Oracle_dantzig_oracle_inequality
-- name    : DantzigSelector.Oracle.dantzig_oracle_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T17:50:00.107884+00:00
-- url     : https://prove2.me/theorems/77e502d9-4a6d-4b6e-b406-93b5f2cc24fc
-- title:
--   Theorem 1.2 — the Dantzig selector is within a $\log p$ factor of the ideal mean squared error
-- statement:
--   Consider the linear model $y=X\beta+z$ (1.1), where $X\in\mathbb R^{n\times p}$ is a deterministic design matrix whose columns $X_j$ are unit-normed, $\beta\in\mathbb R^p$ is a deterministic parameter, and $z=(z_1,\dots,z_n)$ is a vector of independent $N(0,\sigma^2)$ random variables with $\sigma>0$. Let $S\ge1$ with $3S\le p$, and write $\delta=\delta_{2S}$ and $\theta=\theta_{S,2S}$ for the restricted isometry and restricted orthogonality constants of $X$. Let $C_2$ be the constant (1.14),
--   $$C_2=\frac{2C_0}{1-\delta-\theta}+\frac{2\theta(1+\delta)}{(1-\delta-\theta)^2}+\frac{1+\delta}{1-\delta-\theta},\qquad C_0=2\sqrt2\Big(1+\frac{1-\delta^2}{1-\delta-\theta}\Big)+\Big(1+\frac1{\sqrt2}\Big)\frac{(1+\delta)^2}{1-\delta-\theta}.$$
--
--   Choose $t>0$ and $a\ge0$ and set $\lambda_p:=(\sqrt{1+a}+t^{-1})\sqrt{2\log p}$. If $\beta$ is $S$-sparse and $\delta+\theta<1-t$, then with probability exceeding $1-(\sqrt{\pi\log p}\cdot p^a)^{-1}$, a Dantzig selector $\hat\beta$ (an $\ell_1$-minimizer subject to $\|X^*(y-X\tilde\beta)\|_{\ell_\infty}\le\lambda_p\sigma$) exists and every such $\hat\beta$ obeys
--   $$\|\hat\beta-\beta\|_{\ell_2}^2\le C_2^2\cdot\lambda_p^2\cdot\Big(\sigma^2+\sum_{i=1}^p\min(\beta_i^2,\sigma^2)\Big).\qquad(1.13)$$
--
--   The case $a=0$ is the tuning $\lambda_p=(1+t^{-1})\sqrt{2\log p}$ of the theorem's first sentence. The bound says that the Dantzig selector, which knows neither the support of $\beta$ nor which coefficients exceed the noise level, achieves the ideal mean squared error $\sum_i\min(\beta_i^2,\sigma^2)$ of an oracle estimator up to a factor of order $\log p$.
--
--   **Formalization Note** The statement bounds the probability of the bad event "no Dantzig selector exists, or some Dantzig selector violates (1.13)" from above by $(\sqrt{\pi\log p}\cdot p^a)^{-1}$, strictly ("exceeding"); the bad event is not assumed measurable, its outer measure is bounded. $C_2$ and $C_0$ are exactly the printed (1.14), evaluated at the published $\delta_{2S}$ and $\theta_{S,2S}$ of $X$; they do not depend on $t$, $a$, $p$ or $\beta$. $3S\le p$ is the domain of $\theta_{S,2S}$ ((1.5)) and forces $p\ge3$, so $\log p>0$. The noise has law $N(0,\sigma^2)$ coordinatewise with mutually independent coordinates.
-- source:
--   Candès & Tao, The Dantzig Selector: Statistical Estimation When p Is Much Larger than n, arXiv:math/0506081v3, pp. 8-9, Theorem 1.2, Eqs. (1.13)-(1.14); probability as in Theorem 1.1, p. 5

import Mathlib
import Definitions.Def_CandesTao_Decoding_Norms
import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Definitions.Def_DantzigSelector_Sparse_Model
import Definitions.Def_DantzigSelector_Oracle_Model

open MeasureTheory ProbabilityTheory CandesTao.Decoding DantzigSelector.Sparse

namespace DantzigSelector.Oracle

/-- Candès–Tao (2007), Theorem 1.2, pp. 8–9, with the constant `C2` of (1.14) at
`δ = δ_{2S}`, `θ = θ_{S,2S}`. Model (1.1): `y = Xβ + z` with unit-normed columns and
`z_1, …, z_n` i.i.d. `N(0, σ²)`, `σ > 0`. For `t > 0`, `a ≥ 0` and
`λ_p = (√(1 + a) + t⁻¹) √(2 log p)`, if `β` is `S`-sparse and `δ + θ < 1 − t`, then outside an
event of probability less than `(√(π log p) · p^a)⁻¹` a Dantzig selector `β̂` at level `λ_p σ`
exists and every one obeys `‖β̂ − β‖²_{ℓ2} ≤ C2² λ_p² (σ² + ∑_i min(β_i², σ²))` (1.13). -/
theorem dantzig_oracle_inequality {n p : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitNormColumns X)
    (S : ℕ) (hS : 1 ≤ S) (hSp : 3 * S ≤ p) (σ : ℝ) (hσ : 0 < σ)
    (z : Fin n → Ω → ℝ) (hz : ∀ i, HasLaw (z i) (gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) P)
    (hind : iIndepFun z P) (β : Fin p → ℝ) (hβ : IsSparse β S) (t : ℝ) (ht : 0 < t)
    (a : ℝ) (ha : 0 ≤ a)
    (hδθ : restrictedIsometryConst X (2 * S) + restrictedOrthogonalityConst X S (2 * S) < 1 - t) :
    P {ω | ¬ ((∃ b : Fin p → ℝ,
              IsDantzigSelector X (X.mulVec β + fun i => z i ω)
                ((Real.sqrt (1 + a) + t⁻¹) * Real.sqrt (2 * Real.log p) * σ) b) ∧
            ∀ b : Fin p → ℝ,
              IsDantzigSelector X (X.mulVec β + fun i => z i ω)
                ((Real.sqrt (1 + a) + t⁻¹) * Real.sqrt (2 * Real.log p) * σ) b →
              l2Norm (b - β) ^ 2 ≤
                C2 (restrictedIsometryConst X (2 * S)) (restrictedOrthogonalityConst X S (2 * S)) ^ 2 *
                  ((Real.sqrt (1 + a) + t⁻¹) * Real.sqrt (2 * Real.log p)) ^ 2 *
                  (σ ^ 2 + idealMSE β σ))} <
      ENNReal.ofReal (1 / (Real.sqrt (Real.pi * Real.log p) * (p : ℝ) ^ a)) := by sorry

end DantzigSelector.Oracle
