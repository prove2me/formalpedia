-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Real_map_ellipticProduct_neg
-- name    : AutomorphicForm.GL2Real.map_ellipticProduct_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/3c9d5a57-35be-5565-b6c9-7f5c4afae3a6
-- title:
--   Elliptic chart: density ρ³/y⁴ carried to negative determinant
-- statement:
--   The statement concerns the four-dimensional Lebesgue measure `volume` on the space $\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to \mathbb{R}$ of $2\times 2$ real arrays and has no variables or hypotheses. Consider the map that sends an array $p$, with entries written $\rho = p_{00}$, $\varphi = p_{01}$, $y = p_{10}$, $x = p_{11}$, to the array of entries of the invertible matrix
--   $$\begin{pmatrix} \rho\cos\varphi & \rho\sin\varphi \\ -\rho\sin\varphi & \rho\cos\varphi\end{pmatrix}\cdot\left(\begin{pmatrix} y & x \\ 0 & 1\end{pmatrix}\begin{pmatrix} 1 & 0 \\ 0 & -1\end{pmatrix}\right)^{-1}$$
--   when $\rho > 0$ and $y > 0$ (the first factor being `ellipticElt` $\rho\,\varphi$, the second the product of `upperHalfPlaneElt` $x\,y$ with `upperTriangular` $1\,(-1)\,0$), and to the identity matrix otherwise. The assertion is that the push-forward along this map of the measure obtained from `volume` restricted to the set of arrays with $\rho > 0$, $y > 0$ and $0 < \varphi < 2\pi$ by multiplying by the density $p \mapsto \rho^3/y^4$ (via `ENNReal.ofReal`) equals `volume` restricted to the set of arrays $m$ with $m_{00}m_{11} - m_{01}m_{10} < 0$, i.e. to the matrices of negative determinant.
--
--   This is the change-of-variables (Jacobian) computation for the polar, or elliptic, coordinate chart on the negative-determinant sheet of $\mathrm{GL}_2(\mathbb{R})$, expressing Lebesgue measure there as the image of the explicit density $\rho^3/y^4$ on the parameter domain. It is used in [`AutomorphicForm.GL2Real.orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div`](thm.html#AutomorphicForm.GL2Real.orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div), where orbital integrals over $\mathrm{GL}_2(\mathbb{R})$ are rewritten as integrals in the split and elliptic coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Real_map_ellipticProduct_neg.lean

import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MeasureTheory

theorem AutomorphicForm.GL2Real.map_ellipticProduct_neg :
    Measure.map
      (fun p : Fin 2 → Fin 2 → ℝ => Matrix.of.symm
      (((if h : 0 < p 0 0 ∧ 0 < p 1 0 then
            ellipticElt (p 0 0) (p 0 1) h.1 *
              (upperHalfPlaneElt (p 1 1) (p 1 0) h.2 *
                upperTriangular 1 (-1) 0 (mul_ne_zero one_ne_zero (neg_ne_zero.2 one_ne_zero)))⁻¹
          else 1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)))
      ((volume.restrict
        {p : Fin 2 → Fin 2 → ℝ | 0 < p 0 0 ∧ 0 < p 1 0 ∧ 0 < p 0 1 ∧ p 0 1 < 2 * Real.pi}).withDensity
        (fun p : Fin 2 → Fin 2 → ℝ => ENNReal.ofReal (p 0 0 ^ 3 / p 1 0 ^ 4))) =
      volume.restrict
        {m : Fin 2 → Fin 2 → ℝ | m 0 0 * m 1 1 - m 0 1 * m 1 0 < 0} := by sorry
