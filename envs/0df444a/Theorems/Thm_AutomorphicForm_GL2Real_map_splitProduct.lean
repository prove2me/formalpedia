-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Real_map_splitProduct
-- name    : AutomorphicForm.GL2Real.map_splitProduct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/96c529fc-bb4e-5329-a643-460a0ef6ade7
-- title:
--   Split product chart carries |a₁a₂| dλ to Lebesgue measure
-- statement:
--   The statement is closed: no variables or hypotheses. Consider the map $\Phi$ on $2\times 2$ real arrays $p$ (elements of `Fin 2 → Fin 2 → ℝ`) defined as follows. If $p_{00}p_{01}\neq 0$, then $\Phi(p)$ is the matrix underlying the element of $\mathrm{GL}_2(\mathbb{R})$ given by the product of the upper-triangular matrix $\begin{pmatrix} p_{00} & p_{00}p_{11} \\ 0 & p_{01}\end{pmatrix}$ (invertible since $p_{00}p_{01}\neq 0$) with the inverse of the rotation matrix $\begin{pmatrix}\cos p_{10} & \sin p_{10} \\ -\sin p_{10} & \cos p_{10}\end{pmatrix}$ (invertible because $\cos^2+\sin^2=1$); if $p_{00}p_{01}=0$, then $\Phi(p)$ is the identity matrix. Thus the first row of $p$ supplies the diagonal entries $(a_1,a_2)=(p_{00},p_{01})$, while the second row supplies an angle $\theta=p_{10}$ and a parameter $u=p_{11}$ entering through the upper-right entry $a_1u$. The assertion is that the pushforward under $\Phi$ of four-dimensional Lebesgue measure restricted to $\{p : p_{00}p_{01}\neq 0,\ 0<p_{10}<\pi\}$ and given density $|p_{00}p_{01}|$ equals Lebesgue measure on $2\times2$ arrays restricted to $\{m : m_{00}m_{11}-m_{01}m_{10}\neq 0,\ m_{10}\neq 0\}$.
--
--   This is the Jacobian computation for the split (Iwasawa-type) product coordinates on $\mathrm{GL}_2(\mathbb{R})$, identifying the invertible matrices with non-zero lower-left entry with the parameters $(a_1,a_2,\theta,u)$ in the range $a_1a_2\neq0$, $0<\theta<\pi$. It is used in the evaluation of orbital integrals, via [`AutomorphicForm.GL2Real.orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div`](thm.html#AutomorphicForm.GL2Real.orbitalIntegral_eq_splitTransform_div_and_eq_ellipticTransform_div).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Real_map_splitProduct.lean

import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MeasureTheory

theorem AutomorphicForm.GL2Real.map_splitProduct :
    Measure.map
      (fun p : Fin 2 → Fin 2 → ℝ => Matrix.of.symm
      (((if h : p 0 0 * p 0 1 ≠ 0 then
            upperTriangular (p 0 0) (p 0 1) (p 0 0 * p 1 1) h * (rotation (p 1 0))⁻¹
          else 1 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)))
      ((volume.restrict
        {p : Fin 2 → Fin 2 → ℝ | p 0 0 * p 0 1 ≠ 0 ∧ 0 < p 1 0 ∧ p 1 0 < Real.pi}).withDensity
        (fun p : Fin 2 → Fin 2 → ℝ => ENNReal.ofReal |p 0 0 * p 0 1|)) =
      volume.restrict
        {m : Fin 2 → Fin 2 → ℝ | m 0 0 * m 1 1 - m 0 1 * m 1 0 ≠ 0 ∧ m 1 0 ≠ 0} := by sorry
