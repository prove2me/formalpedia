-- Prove2me | Theorems.Thm_CauchyRiemannIndex_loopOp_inner_le
-- name    : CauchyRiemannIndex.loopOp_inner_le
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-23T16:10:11.807471+00:00
-- url     : https://prove2.me/theorems/9fde86ee-d217-4713-99a6-7484bb1e2356
-- title:
--   Spectral gap inequality for the asymptotic loop operator $-J_0\partial_t - S_\infty$
-- statement:
--   Let $S_\infty:\mathbb{R}\to\mathbb{R}^{2n\times 2n}$ be a continuous $1$-periodic loop of symmetric matrices, and let $A=-J_0\frac{d}{dt}-S_\infty(t)$ be the corresponding asymptotic operator acting on $1$-periodic loops $\eta:\mathbb{R}\to\mathbb{R}^{2n}$, with $J_0$ the standard complex structure. Then for every $\mu\in\mathbb{R}$ there is a constant $C\ge0$ such that for every $C^1$ $1$-periodic loop $\eta$,
--   $$\Bigl|\int_0^1\bigl\langle\eta(t),\,(A-\mu)\eta(t)\bigr\rangle\,dt\Bigr|\;\le\;C\int_0^1\bigl|(A-\mu)\eta(t)\bigr|^2\,dt .$$
--   Equivalently, the quadratic form of $A-\mu$ is controlled by the squared $L^2$ norm of $(A-\mu)\eta$. This reflects the fact that $A$ is self-adjoint with discrete spectrum: the kernel of $A-\mu$ contributes nothing to the left-hand side, and on its orthogonal complement $A-\mu$ is bounded below. The estimate is the spectral-gap input in the proof of the linear asymptotic formula (Wendl Thm. 4.8.2).
-- source:
--   Wendl, Lectures on Symplectic Field Theory (2026 notes), §3.1 (asymptotic operators are self-adjoint with discrete spectrum), used in the proof of Theorem 4.8.2; U. Hryniewicz, J. Symplectic Geom. 12 (2014), proof of Theorem 2.11

import Mathlib
import Definitions.Def_CauchyRiemannIndex_Setting

namespace CauchyRiemannIndex

open scoped RealInnerProductSpace

/-- Spectral gap estimate for the loop operator `A = -J₀ d/dt - S∞(t)` on 1-periodic loops: for
every `μ ∈ ℝ` there is `C ≥ 0` with `|⟨η, (A - μ)η⟩_{L²}| ≤ C ‖(A - μ)η‖²_{L²}` for all `C¹`
1-periodic `η`. -/
theorem loopOp_inner_le {n : ℕ} (Sinf : ℝ → Mat n) (hSinf : IsSymLoop Sinf) (μ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η η' : ℝ → Vec n, (∀ t, HasDerivAt η (η' t) t) → Continuous η' →
      Function.Periodic η 1 →
      |∫ t in (0:ℝ)..1, ⟪η t, -(Matrix.toEuclideanLin (J₀ n) (η' t)) -
          Matrix.toEuclideanLin (Sinf t) (η t) - μ • η t⟫| ≤
        C * ∫ t in (0:ℝ)..1, ‖-(Matrix.toEuclideanLin (J₀ n) (η' t)) -
          Matrix.toEuclideanLin (Sinf t) (η t) - μ • η t‖ ^ 2 := by sorry

end CauchyRiemannIndex
