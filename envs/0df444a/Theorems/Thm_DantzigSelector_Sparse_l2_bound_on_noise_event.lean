-- Prove2me | Theorems.Thm_DantzigSelector_Sparse_l2_bound_on_noise_event
-- name    : DantzigSelector.Sparse.l2_bound_on_noise_event
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:40:51.763274+00:00
-- url     : https://prove2.me/theorems/d066dda1-5206-4eed-ac56-37b78dd1ae4a
-- title:
--   Section 3: on the event (3.1), every Dantzig selector obeys $\|\hat\beta-\beta\|_{\ell_2}^2\le C_1^2\lambda_p^2S$
-- statement:
--   Work with noise level $\sigma=1$, as in Section 3. Let $X\in\mathbb R^{n\times p}$ have unit-normed columns, let $S\ge1$ with $3S\le p$, and write $\delta_{2S}$, $\theta_{S,2S}$ for the restricted isometry and orthogonality constants of $X$; assume $\delta_{2S}+\theta_{S,2S}<1$. Let $\beta\in\mathbb R^p$ be $S$-sparse, let $\lambda_p>0$, and let $z\in\mathbb R^n$ be a fixed vector obeying the orthogonality condition (3.1),
--   $$
--   |\langle z,X_j\rangle|\le\lambda_p\qquad\text{for all }1\le j\le p .
--   $$
--   Then every Dantzig selector $\hat\beta$ at level $\lambda_p$ with data $y=X\beta+z$ satisfies
--   $$
--   \|\hat\beta-\beta\|_{\ell_2}^2\le C_1^2\cdot\lambda_p^2\cdot S,\qquad C_1=\frac{4}{1-\delta_{2S}-\theta_{S,2S}} .
--   $$
--
--   This is the deterministic content of Theorem 1.1, announced on p. 15 as "if (3.1) holds, then (1.10) holds" and proved on pp. 18–19 from (3.2), (3.3) and Lemma 3.1. The probabilistic part of Theorem 1.1 only has to show that (3.1) holds with large probability.
--
--   **Formalization Note** The bound is stated with a general $\lambda_p>0$, the paper's proviso that $\lambda_p^2$ replaces $2\log p$ in (1.10). The paper prints $C_1=4/(1-\delta_S-\theta_{S,2S})$ in Theorem 1.1, but its proof applies Lemma 3.1, whose $\delta$ is $\delta_{2S}$, and yields $C_1=4/(1-\delta_{2S}-\theta_{S,2S})$; since $\delta_S\le\delta_{2S}$, the printed constant claims more than the proof gives, and the constant the proof establishes is stated here.
-- source:
--   Candès & Tao, The Dantzig Selector: Statistical Estimation When p Is Much Larger than n, arXiv:math/0506081v3, p. 15, Section 3 ("if (3.1) holds, then (1.10) holds"), proof on pp. 18–19, Section 3.2

import Mathlib
import Definitions.Def_CandesTao_Decoding_Norms
import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Definitions.Def_DantzigSelector_Sparse_Model
open CandesTao.Decoding

namespace DantzigSelector.Sparse

/-- Section 3, p. 15, "(3.1) implies (1.10)" (σ = 1): for unit-normed columns, an `S`-sparse
`β` with `δ_{2S} + θ_{S,2S} < 1`, and a fixed noise vector `z` obeying (3.1),
`|⟨z, X_j⟩| ≤ λ_p` for all `j`, every Dantzig selector `b` at level `λ_p` with data
`y = Xβ + z` obeys `‖b - β‖²_{ℓ2} ≤ C1² λ_p² S` with `C1 = 4 / (1 - δ_{2S} - θ_{S,2S})`. -/
theorem l2_bound_on_noise_event {n p S : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (hX : UnitNormColumns X) (hS : 1 ≤ S) (hSp : 3 * S ≤ p)
    (hRIP : restrictedIsometryConst X (2 * S) + restrictedOrthogonalityConst X S (2 * S) < 1)
    (β : Fin p → ℝ) (hβ : IsSparse β S) (z : Fin n → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (hz : ∀ j : Fin p, |∑ i, X i j * z i| ≤ lam) (b : Fin p → ℝ)
    (hb : IsDantzigSelector X (X.mulVec β + z) lam b) :
    l2Norm (b - β) ^ 2 ≤
      (4 / (1 - restrictedIsometryConst X (2 * S) - restrictedOrthogonalityConst X S (2 * S))) ^ 2
        * lam ^ 2 * S := by sorry

end DantzigSelector.Sparse
