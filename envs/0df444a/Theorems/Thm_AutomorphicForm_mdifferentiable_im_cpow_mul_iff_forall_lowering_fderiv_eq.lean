-- Prove2me | Theorems.Thm_AutomorphicForm_mdifferentiable_im_cpow_mul_iff_forall_lowering_fderiv_eq
-- name    : AutomorphicForm.mdifferentiable_im_cpow_mul_iff_forall_lowering_fderiv_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/9dbcf84a-579a-520d-9709-881b5c71b533
-- title:
--   Holomorphy of y^σF versus the lowering eigenvalue equation
-- statement:
--   Let $F$ be a complex-valued function of a real $2\times 2$ matrix, $k$ an integer and $c_0,\sigma$ complex numbers. For $z$ in the upper half-plane write $s(z)=\bigl(\begin{smallmatrix} \operatorname{Im} z & \operatorname{Re} z\\ 0&1\end{smallmatrix}\bigr)$ for the Iwasawa section. Assume that at every point $s(z)$: $F$ is differentiable over $\mathbb{R}$; $F\bigl(s(z)\,r(\theta)\bigr)=e^{ik\theta}F(s(z))$ for all real $\theta$, where $r(\theta)=\bigl(\begin{smallmatrix}\cos\theta&\sin\theta\\-\sin\theta&\cos\theta\end{smallmatrix}\bigr)$; and $F(t\cdot s(z))=t^{c_0}F(s(z))$ for all real $t>0$, the power being the principal complex power of $t$. Then the function $z\mapsto (\operatorname{Im} z)^{\sigma}F(s(z))$ on the upper half-plane is differentiable with respect to the complex model on the domain and on $\mathbb{C}$ (that is, holomorphic) if and only if for every $z$ in the upper half-plane
--   $$\tfrac12\Bigl(DF(s(z))\bigl[s(z)\bigl(\begin{smallmatrix}1&0\\0&-1\end{smallmatrix}\bigr)\bigr]-i\,DF(s(z))\bigl[s(z)\bigl(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\bigr)\bigr]\Bigr)=-\Bigl(\sigma+\frac{k+c_0}{2}\Bigr)F(s(z)),$$
--   where $DF(s(z))$ denotes the Fréchet derivative of $F$ over $\mathbb{R}$ at $s(z)$. The hypotheses and the right-hand condition are imposed only at the points of the section.
--
--   This is the classical dictionary, in two-sided form with an arbitrary normalising exponent $\sigma$, between weight-$k$ functions on $\mathrm{GL}_2(\mathbb{R})$ annihilated (or eigen-) by the Maass lowering operator $L=\tfrac12(\hat H-iS)$ acting by right translation and holomorphic functions on the upper half-plane; taking $\sigma=-(k+c_0)/2$ gives the annihilation case. It is used to prove [`AutomorphicForm.isArchLowestWeightAt_iff_isArchLoweringAnnihilatedAt_of_hasArchCharacterAt`](thm.html#AutomorphicForm.isArchLowestWeightAt_iff_isArchLoweringAnnihilatedAt_of_hasArchCharacterAt), the archimedean lowest-weight criterion in the analytic input to the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_mdifferentiable_im_cpow_mul_iff_forall_lowering_fderiv_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Manifold

theorem AutomorphicForm.mdifferentiable_im_cpow_mul_iff_forall_lowering_fderiv_eq
    (F : (Fin 2 → Fin 2 → ℝ) → ℂ) (k : ℤ) (c₀ σ : ℂ)
    (hF : ∀ z : UpperHalfPlane,
      DifferentiableAt ℝ F (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ))
    (hk : ∀ (z : UpperHalfPlane) (θ : ℝ),
      F ((!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) *
          !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]) =
        Complex.exp (Complex.I * k * θ) * F (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ))
    (hc : ∀ (z : UpperHalfPlane) (t : ℝ), 0 < t →
      F (t • (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)) =
        ((t : ℂ) ^ c₀) * F (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : UpperHalfPlane =>
        (((z.im : ℝ) : ℂ) ^ σ) * F (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)) ↔
      ∀ z : UpperHalfPlane,
        (fderiv ℝ F (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)
              ((!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 0; 0, -1]) -
            Complex.I *
              fderiv ℝ F (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)
                ((!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![0, 1; 1, 0])) / 2 =
          -(σ + (k + c₀) / 2) * F (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by sorry
