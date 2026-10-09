-- Prove2me | Theorems.Thm_DantzigSelector_Sparse_dantzig_sparse_l2_bound
-- name    : DantzigSelector.Sparse.dantzig_sparse_l2_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T08:40:59.589345+00:00
-- url     : https://prove2.me/theorems/6283cb11-a2ec-4abb-8cf1-60daf44bf507
-- title:
--   Theorem 1.1 — the Dantzig selector's $\ell_2$ error is $O(\log p\cdot S\cdot\sigma^2)$
-- statement:
--   Consider the linear model $y=X\beta+z$ of (1.1), where $X\in\mathbb R^{n\times p}$ is a deterministic design matrix with unit-normed columns, $\beta\in\mathbb R^p$ is a deterministic vector of parameters, and $z=(z_1,\dots,z_n)$ is a vector of independent $N(0,\sigma^2)$ random variables with $\sigma>0$. Let $S\ge1$ with $3S\le p$, and suppose $\beta$ is $S$-sparse and
--   $$
--   \delta_{2S}+\theta_{S,2S}<1 ,
--   $$
--   where $\delta_{2S}$ is the restricted isometry constant (1.3) and $\theta_{S,2S}$ the restricted orthogonality constant (1.5) of $X$. Fix $a\ge0$ and choose
--   $$
--   \lambda_p:=\sqrt{2(1+a)\log p}
--   $$
--   in the Dantzig selector (DS), whose constraint is $\|X^*(y-X\tilde\beta)\|_{\ell_\infty}\le\lambda_p\sigma$. Then, with probability exceeding $1-\bigl(\sqrt{\pi\log p}\cdot p^a\bigr)^{-1}$, the program (DS) has a solution and every solution $\hat\beta$ obeys
--   $$
--   \|\hat\beta-\beta\|_{\ell_2}^2\le C_1^2\cdot\lambda_p^2\cdot S\cdot\sigma^2,\qquad C_1=\frac{4}{1-\delta_{2S}-\theta_{S,2S}} .
--   $$
--   For $a=0$ this is (1.10), $\|\hat\beta-\beta\|_{\ell_2}^2\le C_1^2\cdot(2\log p)\cdot S\cdot\sigma^2$.
--
--   The theorem says that, up to the factor $\log p$, the Dantzig selector estimates an $S$-sparse parameter from $n\ll p$ noisy observations with the mean squared error $S\sigma^2$ an oracle knowing the support would achieve, by solving a linear program.
--
--   **Formalization Note** The paper prints $C_1=4/(1-\delta_S-\theta_{S,2S})$, but its proof (pp. 18–19) goes through Lemma 3.1, whose constant is $\delta=\delta_{2S}$, and establishes $C_1=4/(1-\delta_{2S}-\theta_{S,2S})$; since $\delta_S\le\delta_{2S}$ the printed constant claims more than is proved, and the constant the proof gives is stated. The failure event includes "(DS) has no solution", so the statement cannot hold vacuously. Its probability is the outer measure of that event, and the bound is strict, as in the paper's "exceeding". The noise is a family `z : Fin n → Ω → ℝ` of mutually independent random variables with law `gaussianReal 0 σ²`. The hypotheses $1\le S$ and $3S\le p$ record that $\theta_{S,2S}$ is defined only for $S+2S\le p$; they force $p\ge3$, so $\log p>0$.
-- source:
--   Candès & Tao, The Dantzig Selector: Statistical Estimation When p Is Much Larger than n, arXiv:math/0506081v3, p. 5, Theorem 1.1, Eq. (1.10) (constant corrected to δ_2S as in the proof, pp. 18–19)

import Mathlib
import Definitions.Def_CandesTao_Decoding_Norms
import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Definitions.Def_DantzigSelector_Sparse_Model
open CandesTao.Decoding
open MeasureTheory ProbabilityTheory

namespace DantzigSelector.Sparse

/-- Theorem 1.1, with the constant its proof gives, `C1 = 4 / (1 - δ_{2S} - θ_{S,2S})`.
Model `y = Xβ + z` with `z_1, …, z_n` independent `N(0, σ²)`, unit-normed columns, `β`
`S`-sparse, `δ_{2S} + θ_{S,2S} < 1`. For every `a ≥ 0`, with `λ_p = √(2(1+a) log p)`, the
probability that no Dantzig selector at level `λ_p σ` exists, or that some Dantzig selector `β̂`
violates `‖β̂ - β‖²_{ℓ2} ≤ C1² λ_p² S σ²`, is less than `(√(π log p) · p^a)⁻¹`. -/
theorem dantzig_sparse_l2_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n p S : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (hX : UnitNormColumns X) (hS : 1 ≤ S) (hSp : 3 * S ≤ p)
    (hRIP : restrictedIsometryConst X (2 * S) + restrictedOrthogonalityConst X S (2 * S) < 1)
    (β : Fin p → ℝ) (hβ : IsSparse β S) (σ : ℝ) (hσ : 0 < σ)
    (z : Fin n → Ω → ℝ) (hz : ∀ i, HasLaw (z i) (gaussianReal 0 (σ ^ 2).toNNReal) P)
    (hind : iIndepFun z P) (a : ℝ) (ha : 0 ≤ a) :
    P {ω | ¬ ((∃ b : Fin p → ℝ,
              IsDantzigSelector X (X.mulVec β + fun i => z i ω)
                (Real.sqrt (2 * (1 + a) * Real.log p) * σ) b) ∧
            ∀ b : Fin p → ℝ,
              IsDantzigSelector X (X.mulVec β + fun i => z i ω)
                (Real.sqrt (2 * (1 + a) * Real.log p) * σ) b →
              l2Norm (b - β) ^ 2 ≤
                (4 / (1 - restrictedIsometryConst X (2 * S)
                    - restrictedOrthogonalityConst X S (2 * S))) ^ 2
                  * Real.sqrt (2 * (1 + a) * Real.log p) ^ 2 * S * σ ^ 2)} <
      ENNReal.ofReal (1 / (Real.sqrt (Real.pi * Real.log p) * (p : ℝ) ^ a)) := by sorry

end DantzigSelector.Sparse
