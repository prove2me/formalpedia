-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight
-- name    : AutomorphicForm.GL2Real.exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/4633eb5f-3e27-5f71-bc30-477dea3ff504
-- title:
--   Low Chebyshev modes of the elliptic transform on GL₂(ℝ)
-- statement:
--   There exists a real constant $\kappa>0$ with the following property. Let $m$ be a natural number and let $f\colon GL_2(\mathbb{R})\to\mathbb{C}$ be continuous with compact support, and assume $f$ is bi-equivariant for the subgroup `rowIsometrySubgroup₀ ℝ` of $GL_2(\mathbb{R})$ against the unit-valued character `archWeightCharℝ (m : ℤ)`, i.e. $f(k_1gk_2)=\chi_m(k_1)\chi_m(k_2)f(g)$ for all $k_1,k_2$ in that subgroup and all $g$. Then for every natural number $j$ with $2\le j\le m+1$ and every $r>0$, the interval integral over $\theta\in(0,\pi)$ of `ellipticTransform f r θ` times the value at $\cos\theta$ of the Chebyshev polynomial of the second kind `Polynomial.Chebyshev.U ℝ ((j : ℤ) - 2)` equals $-\kappa\,r^{-1}$ times the integral over $t\in\mathbb{R}$ of $\sinh((j-1)|t|)$ against `splitTransform f (r * Real.exp t) (r * Real.exp (-t))` $+\,(-1)^j\,$`splitTransform f (-(r * Real.exp t)) (-(r * Real.exp (-t)))`. Here, for $r>0$, `ellipticTransform f r θ` is $4\sin^2\theta$ times the integral over $y>0$ and $x\in\mathbb{R}$ of $y^{-2}\bigl(f(n\,a_{r,\theta}\,n^{-1})+f(n\,a_{r,-\theta}\,n^{-1})\bigr)$ with $n=\begin{pmatrix}y&x\\0&1\end{pmatrix}$ and $a_{r,\theta}=r\begin{pmatrix}\cos\theta&\sin\theta\\-\sin\theta&\cos\theta\end{pmatrix}$, and for $a_1a_2\neq0$, `splitTransform f a₁ a₂` is $(2\pi)^{-1}$ times the integral over $\theta\in(0,2\pi)$ and $u\in\mathbb{R}$ of $f\bigl(k(\theta)\begin{pmatrix}a_1&u\\0&a_2\end{pmatrix}k(\theta)^{-1}\bigr)$, $k(\theta)$ the rotation matrix; both transforms are $0$ outside those ranges. The constant $\kappa$ is asserted to exist, not computed.
--
--   This is Weyl's integration formula on $GL_2(\mathbb{R})$ in orbital-transform form: pairing the elliptic transform of a function of two-sided weight-$m$ type against the character $U_{j-2}(\cos\theta)$ of the $(j-2)$-nd symmetric power, for $j\le m+1$, reproduces a hyperbolic (split) integral against $\sinh((j-1)|t|)$. It feeds the construction of the discrete-series pairing, being cited by [`AutomorphicForm.GL2Real.exists_contDiff_splitTransform_eq_ellipticTransform_eq_of_discreteSeriesPairing`](thm.html#AutomorphicForm.GL2Real.exists_contDiff_splitTransform_eq_ellipticTransform_eq_of_discreteSeriesPairing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.lean

import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm AutomorphicForm.GL2Real

theorem AutomorphicForm.GL2Real.exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (m : ℕ) (f : GL (Fin 2) ℝ → ℂ), Continuous f → HasCompactSupport f →
      (∀ (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
        f ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
          ((archWeightCharℝ (m : ℤ) k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ (m : ℤ) k₂ : ℂˣ) : ℂ) * f g) →
      ∀ j : ℕ, 2 ≤ j → j ≤ m + 1 → ∀ r : ℝ, 0 < r →
        (∫ θ in (0 : ℝ)..Real.pi,
            ellipticTransform f r θ * (((Polynomial.Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) =
          -(κ : ℂ) * (1 / r : ℂ) *
            ∫ t : ℝ, (Real.sinh (((j : ℝ) - 1) * |t|) : ℂ) *
              (splitTransform f (r * Real.exp t) (r * Real.exp (-t)) +
                (-1 : ℂ) ^ j * splitTransform f (-(r * Real.exp t)) (-(r * Real.exp (-t)))) := by sorry
