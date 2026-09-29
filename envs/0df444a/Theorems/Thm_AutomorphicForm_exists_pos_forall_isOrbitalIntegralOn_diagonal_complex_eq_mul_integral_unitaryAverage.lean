-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_diagonal_complex_eq_mul_integral_unitaryAverage
-- name    : AutomorphicForm.exists_pos_forall_isOrbitalIntegralOn_diagonal_complex_eq_mul_integral_unitaryAverage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/515b1e11-62a7-54e2-81a7-437c486eb131
-- title:
--   Orbital integrals at regular diagonal elements of GL₂(ℂ)
-- statement:
--   Let $\mu$ be a Haar measure on $\mathrm{GL}_2(\mathbb{C})$ for its Borel $\sigma$-algebra, let $a_1,a_2\in\mathbb{C}$ be non-zero and distinct, let $\gamma\in\mathrm{GL}_2(\mathbb{C})$ be an element whose underlying matrix is $\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}$, and let $\tau$ be a Haar measure on the centraliser of $\{\gamma\}$ in $\mathrm{GL}_2(\mathbb{C})$, again with its Borel $\sigma$-algebra. Then there is a real $\kappa>0$, depending only on these data, with the following property: for every continuous $f\colon\mathrm{GL}_2(\mathbb{C})\to\mathbb{C}$ with compact support and every $I\in\mathbb{C}$ which is an orbital-integral value of $f$ at $\gamma$ relative to $(\mu,\tau)$ — that is, for which there exists $w\colon\mathrm{GL}_2(\mathbb{C})\to\mathbb{R}$ that is non-negative, Borel measurable and compactly supported, satisfies $\int_{T_\gamma}w(tx)\,d\tau(t)=1$ for every $x$ with $f(x^{-1}\gamma x)\neq 0$, and satisfies $I=\int f(x^{-1}\gamma x)\,w(x)\,d\mu(x)$ — one has $$I=\kappa\int_{\mathbb{C}}\mathrm{unitaryAverage}\Bigl(k\mapsto f\bigl(k^{-1}\begin{pmatrix}a_1&v\\0&a_2\end{pmatrix}k\bigr)\Bigr)\,dv,$$ the integrand being set to $0$ should $\det\begin{pmatrix}a_1&v\\0&a_2\end{pmatrix}$ vanish (which here it never does, as $a_1a_2\neq0$), $dv$ being the volume measure on $\mathbb{C}$, and `unitaryAverage` $F$ denoting the normalised iterated integral $\frac{1}{4\pi^3}\int_0^{2\pi}\!\!\int_0^{\pi/2}\!\!\int_0^{2\pi}\!\!\int_0^{2\pi}\sin\eta\cos\eta\,F(\mathrm{unitaryElt}\,\psi\,\eta\,\xi_1\,\xi_2)$ over the explicit four-parameter parametrisation `unitaryElt` of the unitary matrices. In particular the value $I$ does not depend on the choice of section function $w$.
--
--   This is the archimedean computation of the orbital integral of a continuous compactly supported test function at a regular split element of $\mathrm{GL}_2(\mathbb{C})$: up to a positive constant it equals the integral over the unipotent direction of the average of $f$ over conjugates by unitary matrices, the constant absorbing the normalisations of $\mu$ and $\tau$ and the factor $|a_1-a_2|^{2}$ coming from the change of variable $v=(a_1-a_2)y$. It is used in the complex-place vanishing statement [`AutomorphicForm.apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegralOn_complex_eq_zero`](thm.html#AutomorphicForm.apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegralOn_complex_eq_zero), where vanishing of all regular semisimple orbital integrals is converted into vanishing of the function itself.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_diagonal_complex_eq_mul_integral_unitaryAverage.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Twisted
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_pos_forall_isOrbitalIntegralOn_diagonal_complex_eq_mul_integral_unitaryAverage
    (μ : @Measure (GL (Fin 2) ℂ) (glBorelOf ℂ)) (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℂ) μ)
    (a₁ a₂ : ℂ) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (hne : a₁ ≠ a₂)
    (γ : GL (Fin 2) ℂ) (hγ : (γ : Matrix (Fin 2) (Fin 2) ℂ) = !![a₁, 0; 0, a₂])
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) (centralizerBorel ℂ γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℂ γ) τ) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ f : GL (Fin 2) ℂ → ℂ, Continuous f → HasCompactSupport f →
        ∀ I : ℂ, IsOrbitalIntegralOn ℂ μ γ τ f I →
          I = (κ : ℂ) * ∫ v : ℂ, unitaryAverage (fun k =>
            if h : Matrix.det !![a₁, v; 0, a₂] ≠ 0 then
              f (k⁻¹ * Matrix.GeneralLinearGroup.mkOfDetNeZero _ h * k) else 0) := by sorry
