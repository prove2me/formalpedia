-- Prove2me | Theorems.Thm_CaiCandesShen_Convergence_lagrangian_argmin_eq
-- name    : CaiCandesShen.Convergence.lagrangian_argmin_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:15:21.92708+00:00
-- url     : https://prove2.me/theorems/eb185053-8d90-4b3f-87e1-91d2d90fd639
-- title:
--   Eq. (2.14) — the minimizers of the Lagrangian of (2.8) are those of $\tau\|X\|_*+\tfrac12\|X-P_\Omega Y\|_F^2$
-- statement:
--   Let $\tau>0$, $\Omega$ an index set, and $M, Y\in\mathbb R^{n_1\times n_2}$. The Lagrangian of problem (2.8) is
--   $$\mathcal L(X,Y)=f_\tau(X)+\langle Y,P_\Omega(M-X)\rangle,\qquad f_\tau(X)=\tau\|X\|_*+\tfrac12\|X\|_F^2 .$$
--   Then
--   $$\arg\min_X\ f_\tau(X)+\langle Y,P_\Omega(M-X)\rangle=\arg\min_X\ \tau\|X\|_*+\tfrac12\|X-P_\Omega Y\|_F^2,$$
--   as sets of minimizers.
--
--   Combined with Theorem 2.1, this identifies the minimizer of the Lagrangian as $\mathcal D_\tau(P_\Omega(Y))$, which is how the SVT iteration (2.7) is recognized as Uzawa's algorithm for (2.8).
--
--   **Formalization Note** Both sides are stated as sets $\{X : \forall X',\ \phi(X)\le\phi(X')\}$ of global minimizers, so the statement asserts equality of the two argmin sets, as printed.
-- source:
--   Cai, Candès, Shen, A Singular Value Thresholding Algorithm for Matrix Completion, SIAM J. Optim. 20 (2010), p. 1964, §2.4, Eq. (2.14)

import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Basic

namespace CaiCandesShen.Convergence

/-- Eq. (2.14), p. 1964: for every `Y`, the minimizers over `X` of the Lagrangian
`f_τ(X) + ⟨Y, P_Ω(M - X)⟩` of problem (2.8) are exactly the minimizers of
`τ‖X‖_* + ½‖X - P_Ω Y‖_F²`. -/
theorem lagrangian_argmin_eq {n₁ n₂ : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (Ω : Finset (Fin n₁ × Fin n₂)) (M Y : Mat n₁ n₂) :
    {X : Mat n₁ n₂ | ∀ X' : Mat n₁ n₂,
        fτ τ X + frobInner Y (projΩ Ω (M - X)) ≤ fτ τ X' + frobInner Y (projΩ Ω (M - X'))} =
      {X : Mat n₁ n₂ | ∀ X' : Mat n₁ n₂,
        τ * nuclearNorm X + 1 / 2 * frobNorm (X - projΩ Ω Y) ^ 2 ≤
          τ * nuclearNorm X' + 1 / 2 * frobNorm (X' - projΩ Ω Y) ^ 2} := by sorry

end CaiCandesShen.Convergence
