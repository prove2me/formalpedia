-- Prove2me | Theorems.Thm_DantzigSelector_Sparse_tube_constraint
-- name    : DantzigSelector.Sparse.tube_constraint
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T08:40:19.178475+00:00
-- url     : https://prove2.me/theorems/3b1ece2f-cd27-49b6-8f3b-84339f6fe945
-- title:
--   Eq. (3.3) — the tube constraint $\|X^*Xh\|_{\ell_\infty}\le2\lambda_p$
-- statement:
--   Work with noise level $\sigma=1$, as in Section 3. Let $X\in\mathbb R^{n\times p}$ have unit-normed columns, $\beta\in\mathbb R^p$, $z\in\mathbb R^n$ and $y=X\beta+z$. Suppose the noise obeys the orthogonality condition (3.1) at level $\lambda_p$,
--   $$
--   |\langle z,X_j\rangle|\le\lambda_p\qquad\text{for all }1\le j\le p,
--   $$
--   and let $\hat\beta$ be feasible for the Dantzig selector at level $\lambda_p$, i.e. $|\langle y-X\hat\beta,X_j\rangle|\le\lambda_p$ for all $j$. Then $h=\hat\beta-\beta$ obeys
--   $$
--   \|X^*Xh\|_{\ell_\infty}=\max_{1\le j\le p}|\langle Xh,X_j\rangle|\le2\lambda_p .
--   $$
--
--   This is the second geometric constraint on the error $h$ in the proof of Theorem 1.1: together with the cone constraint (3.2), it confines $h$ to a set whose $\ell_2$ radius is controlled by Lemma 3.1.
--
--   **Formalization Note** The $\ell_\infty$ bound is stated for each coordinate $j$. Only feasibility of $\hat\beta$ is assumed, not optimality.
-- source:
--   Candès & Tao, The Dantzig Selector: Statistical Estimation When p Is Much Larger than n, arXiv:math/0506081v3, pp. 15–16, Section 3.1, Eq. (3.3) (with (3.1))

import Mathlib
import Definitions.Def_CandesTao_Decoding_Norms
import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Definitions.Def_DantzigSelector_Sparse_Model
open CandesTao.Decoding

namespace DantzigSelector.Sparse

/-- Eq. (3.3) (σ = 1): if the noise `z` obeys the orthogonality condition (3.1),
`|⟨z, X_j⟩| ≤ λ_p` for all `j`, and `b` is feasible for the Dantzig selector at level `λ_p`
with data `y = Xβ + z`, then `h = b - β` obeys `‖Xᵀ X h‖_{ℓ∞} ≤ 2 λ_p`. -/
theorem tube_constraint {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (β b : Fin p → ℝ)
    (hX : UnitNormColumns X) (z : Fin n → ℝ) (lam : ℝ)
    (hz : ∀ j : Fin p, |∑ i, X i j * z i| ≤ lam)
    (hb : DantzigFeasible X (X.mulVec β + z) lam b) :
    ∀ j : Fin p, |∑ i, X i j * X.mulVec (b - β) i| ≤ 2 * lam := by sorry

end DantzigSelector.Sparse
