-- Prove2me | Theorems.Thm_AutomorphicForm_lowering_fderiv_mul_rotation_eq_exp_mul_of_weight
-- name    : AutomorphicForm.lowering_fderiv_mul_rotation_eq_exp_mul_of_weight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/9d57b0bf-1721-5619-b398-422edbf74955
-- title:
--   Lowering operator L=(H-iS)/2 drops the SO(2)-weight by two
-- statement:
--   Let $F$ be a complex-valued function on the space of real $2\times 2$ matrices (given as functions $\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to \mathbb{R}$ of the matrix entries) and let $k$ be an integer. Assume (i) that $F$ is differentiable as a function of the real entries at every matrix $m$ with $\det m > 0$, and (ii) the weight-$k$ transformation law: for every $m$ with $\det m > 0$ and every real $\theta$, $F\bigl(m\,r(\theta)\bigr) = e^{ik\theta}F(m)$, where $r(\theta) = \begin{pmatrix}\cos\theta & \sin\theta\\ -\sin\theta & \cos\theta\end{pmatrix}$. Fix such an $m$ with $\det m > 0$ and a real $\theta$, and write $\hat H = \begin{pmatrix}1&0\\0&-1\end{pmatrix}$, $S = \begin{pmatrix}0&1\\1&0\end{pmatrix}$, and $(LF)(g) = \tfrac12\bigl(DF(g)[g\hat H] - i\,DF(g)[gS]\bigr)$, with $DF(g)$ the Fréchet derivative of $F$ over $\mathbb{R}$ at $g$ and the brackets denoting evaluation of this derivative at the indicated matrix direction. The conclusion is the identity $(LF)\bigl(m\,r(\theta)\bigr) = e^{i(k-2)\theta}\,(LF)(m)$, all derivatives being taken at the points $m\,r(\theta)$ and $m$ respectively.
--
--   This is the statement that the weight-lowering element $L = \tfrac12(\hat H - iS)$ of $\mathfrak{gl}_2(\mathbb{R})\otimes\mathbb{C}$, acting by right-invariant derivatives, sends a function obeying the weight-$k$ law for the rotation subgroup to one obeying the weight-$(k-2)$ law, the function-level form of $\mathrm{Ad}(r(\theta))L = e^{-2i\theta}L$. It is used in the analysis of archimedean weights: it feeds the characterisation of vectors annihilated by the lowering operator as lowest-weight vectors, and the associated statement about which weights occur in a class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_lowering_fderiv_mul_rotation_eq_exp_mul_of_weight.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.lowering_fderiv_mul_rotation_eq_exp_mul_of_weight
    (F : (Fin 2 → Fin 2 → ℝ) → ℂ) (k : ℤ)
    (hF : ∀ m : Matrix (Fin 2) (Fin 2) ℝ, 0 < m.det → DifferentiableAt ℝ F m)
    (hk : ∀ m : Matrix (Fin 2) (Fin 2) ℝ, 0 < m.det → ∀ θ : ℝ,
      F (m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]) =
        Complex.exp (Complex.I * k * θ) * F m)
    (m : Matrix (Fin 2) (Fin 2) ℝ) (hm : 0 < m.det) (θ : ℝ) :
    (fderiv ℝ F (m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ])
          ((m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]) * !![1, 0; 0, -1]) -
        Complex.I *
          fderiv ℝ F (m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ])
            ((m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]) * !![0, 1; 1, 0])) / 2 =
      Complex.exp (Complex.I * (k - 2) * θ) *
        ((fderiv ℝ F m (m * !![1, 0; 0, -1]) - Complex.I * fderiv ℝ F m (m * !![0, 1; 1, 0])) / 2) := by sorry
