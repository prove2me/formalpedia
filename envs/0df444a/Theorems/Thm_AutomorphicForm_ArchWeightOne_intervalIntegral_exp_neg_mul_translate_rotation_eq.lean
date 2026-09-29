-- Prove2me | Theorems.Thm_AutomorphicForm_ArchWeightOne_intervalIntegral_exp_neg_mul_translate_rotation_eq
-- name    : AutomorphicForm.ArchWeightOne.intervalIntegral_exp_neg_mul_translate_rotation_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/e22266b4-a49f-5c10-8177-2d0a63972b76
-- title:
--   Weight-one Fourier coefficient of a right translate
-- statement:
--   Let $F\colon \mathrm{GL}_2(\mathbb{R})\to\mathbb{C}$ be continuous and assume three conditions. First, $F$ transforms with weight one under rotations on the right: for all $g$ and all reals $a,b$ with $a^2+b^2=1$, $F\bigl(g\cdot\begin{pmatrix}a&b\\-b&a\end{pmatrix}\bigr)=(a+ib)\,F(g)$, the rotation being formed as an invertible matrix via its determinant $a^2+b^2=1\neq 0$. Second, $F$ is homogeneous of degree one for positive scalars: for every $g$ and every unit $t$ of $\mathbb{R}$ with $t>0$, $F(g\cdot t\mathbf{1}_2)=t\,F(g)$. Third, for every $m\in \mathrm{GL}_2(\mathbb{R})$ the function $z\mapsto (\operatorname{Im} z)^{-1}F\bigl(m\cdot\begin{pmatrix}\operatorname{Im} z&\operatorname{Re} z\\0&1\end{pmatrix}\bigr)$ on the upper half-plane is differentiable with respect to the complex model on both sides. Then for all $h,g\in \mathrm{GL}_2(\mathbb{R})$, with $r(\theta)=\begin{pmatrix}\cos\theta&\sin\theta\\-\sin\theta&\cos\theta\end{pmatrix}$,
--   $$\int_0^{2\pi} e^{-i\theta}\,F\bigl(g\,r(\theta)\,h\bigr)\,d\theta = c(h)\,F(g),$$
--   where, in terms of the real entries $h_{ij}$ of $h$, $c(h)=2\pi\cdot \dfrac{2\det h}{(h_{00}+h_{11})+(h_{10}-h_{01})\,i}$ when $\det h>0$, and $c(h)=0$ otherwise.
--
--   This is the concrete function-theoretic form of the statement that the weight-one $\mathrm{SO}(2)$-isotypic component of the space spanned by the right translates of a holomorphic weight-one vector on $\mathrm{GL}_2(\mathbb{R})$ is a line, with the multiple given explicitly as a matrix coefficient of the lowest-weight vector, and vanishing for translations by elements of negative determinant. It is used in the verification of archimedean holomorphy through the criterion [`AutomorphicForm.isArchHolomorphicAt_of_forall_exists_setLIntegral_sub_sum_holomorphic_translate_sq_lt`](thm.html#AutomorphicForm.isArchHolomorphicAt_of_forall_exists_setLIntegral_sub_sum_holomorphic_translate_sq_lt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_ArchWeightOne_intervalIntegral_exp_neg_mul_translate_rotation_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Manifold

theorem AutomorphicForm.ArchWeightOne.intervalIntegral_exp_neg_mul_translate_rotation_eq
    (F : GL (Fin 2) ℝ → ℂ) (hF : Continuous F)
    (hrot : ∀ (g : GL (Fin 2) ℝ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1),
      F (g * Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; -b, a]
        (by rw [Matrix.det_fin_two_of, show a * a - b * -b = a ^ 2 + b ^ 2 by ring, hab]
            exact one_ne_zero)) = (⟨a, b⟩ : ℂ) * F g)
    (hcen : ∀ (g : GL (Fin 2) ℝ) (t : ℝˣ), 0 < (t : ℝ) →
      F (g * Matrix.GeneralLinearGroup.scalar (Fin 2) t) = ((t : ℝ) : ℂ) * F g)
    (hhol : ∀ m : GL (Fin 2) ℝ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
      ((z.im : ℝ) : ℂ)⁻¹ * F (m * Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(z.im : ℝ), (z.re : ℝ); 0, 1] (by simp [Matrix.det_fin_two_of]; exact z.im_ne_zero)))
    (h g : GL (Fin 2) ℝ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, Complex.exp (-(θ * Complex.I)) *
        F (g * Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]
          (by rw [Matrix.det_fin_two_of, show Real.cos θ * Real.cos θ - Real.sin θ * -Real.sin θ
                = Real.cos θ ^ 2 + Real.sin θ ^ 2 by ring, Real.cos_sq_add_sin_sq]
              exact one_ne_zero) * h)) =
      (if 0 < ((Matrix.GeneralLinearGroup.det h : ℝˣ) : ℝ) then
          2 * Real.pi * (2 * (((Matrix.GeneralLinearGroup.det h : ℝˣ) : ℝ) : ℂ) /
            (((h 0 0 + h 1 1 : ℝ) : ℂ) + ((h 1 0 - h 0 1 : ℝ) : ℂ) * Complex.I))
        else 0) * F g := by sorry
