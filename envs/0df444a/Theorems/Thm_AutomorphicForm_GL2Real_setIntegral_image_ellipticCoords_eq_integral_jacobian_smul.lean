-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Real_setIntegral_image_ellipticCoords_eq_integral_jacobian_smul
-- name    : AutomorphicForm.GL2Real.setIntegral_image_ellipticCoords_eq_integral_jacobian_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/a0ae25de-03e0-541e-afd0-033786f7b6b8
-- title:
--   Elliptic coordinates on GL₂(ℝ): change of variables
-- statement:
--   Let $F$ be a real normed vector space (a normed additive commutative group with a real normed space structure). Let $\Psi \colon (\mathbb{R}\times\mathbb{R})\times(\mathbb{R}\times\mathbb{R}) \to (\mathbb{R}\times\mathbb{R})\times(\mathbb{R}\times\mathbb{R})$ be a map assumed to be given, at every point $v$ with coordinates $\rho = v_{1,1}$, $\theta = v_{1,2}$, $x = v_{2,1}$, $y = v_{2,2}$, by $$\Psi(v) = \bigl((\rho\cos\theta - \rho\sin\theta\,x/y,\ \rho\sin\theta\,(x^2+y^2)/y),\ (-(\rho\sin\theta)/y,\ \rho\cos\theta + \rho\sin\theta\,x/y)\bigr),$$ that is, reading the four output coordinates as the entries of a $2\times 2$ real matrix, the matrix $\rho\,g k_\theta g^{-1}$ with $k_\theta$ the rotation of angle $\theta$ and $g$ of rows $(y,x)$, $(0,1)$. Let $D$ be a set of parameters assumed equal to $\{v : 0 < \rho,\ \theta \in (-\pi,\pi),\ \theta \neq 0,\ 0 < y\}$ (no constraint on $x$), and let $f$ be any $F$-valued function on $\mathbb{R}^4$. The conclusion is fourfold: $\Psi$ is injective on $D$; the image $\Psi(D)$ is measurable; $f$ is integrable on $\Psi(D)$ if and only if $v \mapsto (4\rho^3\sin^2\theta/y^2)\cdot f(\Psi(v))$ is integrable on $D$; and $\int_{\Psi(D)} f = \int_D (4\rho^3\sin^2\theta/y^2)\cdot f(\Psi(v))$, the measures being Lebesgue measure on $\mathbb{R}^4$ in both cases.
--
--   This is the coordinate form of the Weyl integration formula for the elliptic set of $\mathrm{GL}_2(\mathbb{R})$ with positive determinant: the image $\Psi(D)$ consists of the matrices with non-real eigenvalues, parametrised by a radius $\rho$, an angle $\theta$ and a point $x + iy$ of the upper half-plane, and the weight $4\rho^3\sin^2\theta/y^2$ is the absolute Jacobian determinant, carrying the Weyl discriminant $4\sin^2\theta$. It is used by [`AutomorphicForm.GL2Real.contDiff_integral_ellipticTransform_entrySlice_mul_chebyshevU`](thm.html#AutomorphicForm.GL2Real.contDiff_integral_ellipticTransform_entrySlice_mul_chebyshevU) to convert angular averages of elliptic orbital transforms against Chebyshev polynomials into integrals over matrix entries with respect to Lebesgue measure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Real_setIntegral_image_ellipticCoords_eq_integral_jacobian_smul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.GL2Real.setIntegral_image_ellipticCoords_eq_integral_jacobian_smul
    (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : (ℝ × ℝ) × (ℝ × ℝ) → (ℝ × ℝ) × (ℝ × ℝ))
    (hΨ : ∀ v, Ψ v =
      ((v.1.1 * Real.cos v.1.2 - v.1.1 * Real.sin v.1.2 * v.2.1 / v.2.2,
          v.1.1 * Real.sin v.1.2 * (v.2.1 ^ 2 + v.2.2 ^ 2) / v.2.2),
        (-(v.1.1 * Real.sin v.1.2) / v.2.2,
          v.1.1 * Real.cos v.1.2 + v.1.1 * Real.sin v.1.2 * v.2.1 / v.2.2)))
    (D : Set ((ℝ × ℝ) × (ℝ × ℝ)))
    (hD : D = {v | 0 < v.1.1 ∧ v.1.2 ∈ Set.Ioo (-Real.pi) Real.pi ∧ v.1.2 ≠ 0 ∧ 0 < v.2.2})
    (f : (ℝ × ℝ) × (ℝ × ℝ) → F) :
    Set.InjOn Ψ D ∧ MeasurableSet (Ψ '' D) ∧
      (IntegrableOn f (Ψ '' D) ↔
        IntegrableOn (fun v => (4 * v.1.1 ^ 3 * Real.sin v.1.2 ^ 2 / v.2.2 ^ 2) • f (Ψ v)) D) ∧
      ∫ w in Ψ '' D, f w = ∫ v in D, (4 * v.1.1 ^ 3 * Real.sin v.1.2 ^ 2 / v.2.2 ^ 2) • f (Ψ v) := by sorry
