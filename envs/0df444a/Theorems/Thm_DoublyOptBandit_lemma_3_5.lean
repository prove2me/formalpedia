-- Prove2me | Theorems.Thm_DoublyOptBandit_lemma_3_5
-- name    : DoublyOptBandit.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:28:38.492472+00:00
-- url     : https://prove2.me/theorems/e6801f00-c1c1-4430-b9f1-151ef2e18a32
-- title:
--   Lemma 3.5 — unbiasedness and bias of the ellipsoidal SPSA estimator (corrected: $(A_i^{-1})^\top$ in part 1, $\sigma_{\max}$ = operator norm)
-- statement:
--   Let $A_j\in\mathbb R^{n_j\times n_j}$ be invertible for every player $j$. Let $w_i$ be uniform on the unit ball $\mathbb B^{n_i}$ and $z_j$ uniform on the unit sphere $\mathbb S^{n_j}$ for every $j$, all independent, put $\hat x_j=x_j+A_jz_j$, and let
--   $$
--   \hat u_i(x)=\mathbb E\big[u_i(x_i+A_iw_i;\hat x_{-i})\big].
--   $$
--   Let $u_i$ be continuous on an open set $U$ that contains every profile $(x_j+A_jy_j)_j$ with $\|y_j\|\le1$ for all $j$. Then
--
--   1. $\hat u_i$ is differentiable in $x_i$ at $x$ and
--   $$
--   \nabla_i\hat u_i(x)=\mathbb E\big[n_i\,u_i(\hat x_i;\hat x_{-i})\,(A_i^{-1})^\top z_i\big],
--   $$
--   which is $\mathbb E[n_i\,u_i(\hat x)\,A_i^{-1}z_i]$ when $A_i$ is symmetric;
--   2. if moreover $u_i$ is differentiable in $x_i$ on $U$ with gradient $v_i$, and $v_i$ is $\ell_i$-Lipschitz on $U$, then
--   $$
--   \|\nabla_i\hat u_i(x)-v_i(x)\|\le\ell_i\sqrt{\textstyle\sum_j\sigma_{\max}(A_j)^2},
--   $$
--   where $\sigma_{\max}(A)$ is the largest singular value of $A$.
--
--   The estimator $\hat v_i$ of Algorithm 2 is therefore an unbiased estimate of the gradient of a smoothed reward whose gradient is close to the true one; the proof of Theorem 3.8 uses both parts with the symmetric matrices $A_i^t$.
--
--   Differences from the source:
--   - correction: ∇ᵢûᵢ(x) = E[nᵢ · uᵢ(x̂ᵢ; x̂₋ᵢ)(Aᵢ)⁻¹zᵢ | x] for every invertible Aᵢ → ∇ᵢûᵢ(x) = E[nᵢ · uᵢ(x̂)((Aᵢ)⁻¹)⊤zᵢ], equal to the printed vector when Aᵢ is symmetric; reason: false as printed for non-symmetric Aᵢ: N = 1, n₁ = 2, A = [[1, 10], [0, 1]], u(y) = y₁, x = 0 give ∇û(0) = e₁ but E[2u(Az)A⁻¹z] = A⁻¹A⊤e₁ = (−99, 10); the proof (p.33) writes Aᵢ∇ûᵢ where the chain rule gives Aᵢ⊤∇ûᵢ
--   - correction: σ_max(A) the largest eigenvalue of A → σ_max(A) the largest singular value (operator norm); reason: false as printed for non-symmetric A: N = 1, n₁ = 2, A = [[1, 10], [0, 1]] (eigenvalues 1), u(y) = −(ℓ/2)max(y₁, 0)², x = 0 give ‖∇û(0)‖ = 2√101ℓ/(3π) ≈ 2.13ℓ > ℓ; the proof (p.33) uses ‖Aw‖ ≤ σ_max(A)‖w‖; the two agree for the symmetric positive definite Aᵢᵗ of Algorithm 2
--   - generalization: uᵢ and vᵢ on the whole space (no domain is named) → uᵢ continuous, and in part 2 differentiable in xᵢ with ℓᵢ-Lipschitz gradient, on an open set U containing the product of the closed ellipsoids xⱼ + AⱼB̄ⁿʲ; reason: U = whole space is the source's reading; this form also applies when uᵢ is only defined near X
--   - generalization: uᵢ concave → concavity not assumed; reason: neither conclusion uses it (proof, Appendix D)
--   - encoding: continuity of uᵢ (Definition 3.1 (i), standing assumption of §3) → uᵢ continuous on U; reason: needed for the expectations to be defined; part of the source's setting
--   - encoding: conditional expectation given x₁, …, x_N; wᵢ ∼ Bⁿⁱ, z₋ᵢ ∼ ∏_{j≠i} Sⁿʲ → x fixed; Bochner integrals on a probability space with W uniform on the ball, each Zⱼ uniform on the sphere (published IsUniformOnUnitSphere), (Zⱼ) independent and independent of W; ûᵢ integrates over all Zⱼ, of which Zᵢ is unused; reason: the same expectations
-- source:
--   Ba, Lin, Zhang & Zhou, Doubly Optimal No-Regret Online Learning in Strongly Monotone Games with Bandit Feedback, arXiv:2112.02856v4, Lemma 3.5, p.14; proof, Appendix D, pp.32–33

import Mathlib
import Definitions.Def_OnlineConvexOpt_BanditConvex_UniformOnUnitSphere_v2
import Definitions.Def_DoublyOptBandit_Smoothing

open scoped InnerProductSpace
open MeasureTheory ProbabilityTheory

namespace DoublyOptBandit

/-- **Lemma 3.5** (the ellipsoidal SPSA estimator; Ba, Lin, Zhang & Zhou, arXiv:2112.02856v4,
Lemma 3.5, p.14), corrected in parts 1 and 2. Let `Aⱼ ∈ ℝ^{nⱼ×nⱼ}` be invertible for every player `j`, let
`wᵢ` be uniform on the unit ball `Bⁿⁱ`, the `zⱼ` uniform on the unit spheres `Sⁿʲ`, all independent,
and let `ûᵢ(x) = E[uᵢ(xᵢ + Aᵢwᵢ; x̂₋ᵢ)]` with `x̂ⱼ = xⱼ + Aⱼzⱼ`. Let `uᵢ` be continuous on an open set
`U` containing every profile `(xⱼ + Aⱼyⱼ)ⱼ` with all `‖yⱼ‖ ≤ 1`. Then
1. `∇ᵢûᵢ(x) = E[nᵢ · uᵢ(x̂ᵢ; x̂₋ᵢ)((Aᵢ)⁻¹)⊤zᵢ]` (which is `E[nᵢ · uᵢ(x̂ᵢ; x̂₋ᵢ)(Aᵢ)⁻¹zᵢ]` when
   `Aᵢ` is symmetric, as in Algorithm 2);
2. if moreover `uᵢ` is differentiable in `xᵢ` on `U` with gradient `vᵢ`, and `vᵢ` is
   `ℓᵢ`-Lipschitz on `U`, then `‖∇ᵢûᵢ(x) − vᵢ(x)‖ ≤ ℓᵢ √(Σⱼ σ_max(Aⱼ)²)`, where `σ_max(A)` is the
   largest singular value (operator norm) of `A`.

**Formalization Note** The expectations are Bochner integrals on a probability space carrying `W`
(for `wᵢ`) and the directions `Z j`; the conditioning "`| x₁, …, x_N`" of the paper means that `x`
is fixed. The paper names no domain for `uᵢ`; the statement is posed on an open set `U` containing
the closed product of the ellipsoids `xⱼ + Aⱼ B̄ⁿʲ` (the paper's global reading is `U = ℝⁿ`).
Concavity of `uᵢ` is not assumed (the conclusion does not use it). Part 1 as printed, with
`(Aᵢ)⁻¹zᵢ`, is false for non-symmetric `Aᵢ`: for `N = 1`, `n₁ = 2`, `A = [[1, 10], [0, 1]]`,
`u(y) = y₁` and `x = 0`, `∇û(0) = e₁` while `E[2u(Az)A⁻¹z] = A⁻¹A⊤e₁ = (−99, 10)`; the proof (p.33)
writes `Aᵢ∇ûᵢ` where the chain rule gives `Aᵢ⊤∇ûᵢ`. The corrected vector `((Aᵢ)⁻¹)⊤zᵢ` agrees with the
printed one for symmetric `Aᵢ`. `σ_max(A)` is "the largest
eigenvalue of A" in the paper; with that reading part 2 is false for non-symmetric `A`
(`N = 1`, `n₁ = 2`, `A = [[1, 10], [0, 1]]`, `u(y) = −(ℓ/2)max(y₁, 0)²`, `x = 0`: `‖∇û(0)‖ =
ℓ·2√101/(3π) ≈ 2.13ℓ > ℓ`); the proof (p.33) uses `‖Aw‖ ≤ σ_max(A)‖w‖`, i.e. the operator norm,
which equals the largest eigenvalue for the symmetric positive definite matrices of Algorithm 2. -/
theorem lemma_3_5 {N : ℕ} (n : Fin N → ℕ) (A : ∀ j, Matrix (Fin (n j)) (Fin (n j)) ℝ)
    (hA : ∀ j, IsUnit (A j)) (U : Set (Joint n)) (hU : IsOpen U) (x : Joint n)
    (hxU : ∀ y : ∀ j, EuclideanSpace ℝ (Fin (n j)), (∀ j, ‖y j‖ ≤ 1) → perturb A x y ∈ U)
    (i : Fin N) (ui : Joint n → ℝ) (hui : ContinuousOn ui U)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → EuclideanSpace ℝ (Fin (n i))) (Z : ∀ j, Ω → EuclideanSpace ℝ (Fin (n j)))
    (hW : IsUniformOnUnitBall P W)
    (hZ : ∀ j, OnlineConvexOpt.BanditConvex.IsUniformOnUnitSphere P (Z j))
    (hZind : iIndepFun Z P) (hWZ : IndepFun W (fun ω j => Z j ω) P) :
    HasGradientAt (fun y => smoothedReward P i W Z A ui (update x i y))
        (∫ ω, ((n i : ℝ) * ui (perturb A x (fun j => Z j ω))) •
          Matrix.toEuclideanLin (Matrix.transpose (A i)⁻¹) (Z i ω) ∂P) (x i) ∧
      ∀ (vi : Joint n → EuclideanSpace ℝ (Fin (n i))) (ℓi : ℝ),
        (∀ y ∈ U, HasGradientAt (fun y' => ui (update y i y')) (vi y) (y i)) →
        (∀ y ∈ U, ∀ y' ∈ U, ‖vi y - vi y'‖ ≤ ℓi * ‖y - y'‖) →
        ‖gradient (fun y => smoothedReward P i W Z A ui (update x i y)) (x i) - vi x‖ ≤
          ℓi * Real.sqrt (∑ j, sigmaMax (A j) ^ 2) := by sorry

end DoublyOptBandit
