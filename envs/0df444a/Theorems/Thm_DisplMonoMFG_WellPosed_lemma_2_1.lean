-- Prove2me | Theorems.Thm_DisplMonoMFG_WellPosed_lemma_2_1
-- name    : DisplMonoMFG.WellPosed.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:31.592248+00:00
-- url     : https://prove2.me/theorems/bb970720-c5b0-4ac4-82f9-31cef0269530
-- title:
--   Lemma 2.1 — $\partial_{\tilde x\mu}U(\mu,\tilde x)$ is a symmetric matrix for $U\in\mathcal C^2(\mathcal P_2)$
-- statement:
--   Let $U\in\mathcal C^2(\mathcal P_2)$, with jointly continuous global versions of $\partial_\mu U(\mu,\tilde x)$, $\partial_{\tilde x\mu}U(\mu,\tilde x)$ and $\partial_{\mu\mu}U(\mu,\tilde x,\bar x)$. Then for every $(\mu,\tilde x)\in\mathcal P_2\times\mathbb R^d$ the matrix $\partial_{\tilde x\mu}U(\mu,\tilde x)$ is symmetric:
--   $$
--   \big\langle\partial_{\tilde x\mu}U(\mu,\tilde x)\,b,\,a\big\rangle=\big\langle\partial_{\tilde x\mu}U(\mu,\tilde x)\,a,\,b\big\rangle\qquad\text{for all }a,b\in\mathbb R^d.
--   $$
--
--   The proof of Theorem 4.1 uses this symmetry when it computes the evolution of the displacement monotonicity form along the solution.
--
--   **Formalization Note** The matrix is stored as a bilinear form, with the $\tilde x$-direction first. The statement concerns arbitrary jointly continuous witnesses, which are unique.
-- source:
--   Gangbo, Mészáros, Mou, Zhang, Mean field games master equations with nonseparable Hamiltonians and displacement monotonicity, Ann. Probab. 50 (2022), Lemma 2.1, p. 2184

import Mathlib
import Definitions.Def_DisplMonoMFG_WellPosed_Regularity

open MeasureTheory

namespace DisplMonoMFG.WellPosed

/-- Gangbo, Mészáros, Mou, Zhang, Ann. Probab. 50 (2022), Lemma 2.1, p. 2184 (PDF p. 7):
for any `U ∈ 𝒞²(𝒫₂)` and `(μ, x̃) ∈ 𝒫₂ × ℝ^d`, `∂_x̃μ U(μ, x̃)` is a symmetric matrix.
Here `DyDm μ x̃ a b` is the bilinear form of the matrix `∂_x̃μ U(μ, x̃)` (`a` the `x̃`-direction,
`b` the direction of `∂_μ U`), for any jointly continuous witnesses of `U ∈ 𝒞²(𝒫₂)`. -/
theorem lemma_2_1 {d : ℕ} (U : P2 d → ℝ) (Dm : P2 d → E d → (E d →L[ℝ] ℝ))
    (DyDm : P2 d → E d → (E d →L[ℝ] E d →L[ℝ] ℝ))
    (Dmm : P2 d → E d → E d → (E d →L[ℝ] E d →L[ℝ] ℝ))
    (hU : IsC2P U Dm DyDm Dmm) :
    ∀ (μ : P2 d) (y a b : E d), DyDm μ y a b = DyDm μ y b a := by sorry

end DisplMonoMFG.WellPosed
