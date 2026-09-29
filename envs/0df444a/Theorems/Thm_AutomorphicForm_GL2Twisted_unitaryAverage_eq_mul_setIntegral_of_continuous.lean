-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Twisted_unitaryAverage_eq_mul_setIntegral_of_continuous
-- name    : AutomorphicForm.GL2Twisted.unitaryAverage_eq_mul_setIntegral_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/ef4e110f-7861-5be9-8407-210676a49c9b
-- title:
--   Hopf-coordinate average over U(2) as an integral over ψ∈(0,π)
-- statement:
--   For real parameters $\psi,\eta,\xi_1,\xi_2$ let $k(\psi,\eta,\xi_1,\xi_2)$ denote the element `unitaryElt` of $\mathrm{GL}_2(\mathbb{C})$ given by the matrix $$e^{i\psi}\begin{pmatrix}\cos\eta\, e^{i\xi_1} & \sin\eta\, e^{i\xi_2}\\ -\sin\eta\, e^{-i\xi_2} & \cos\eta\, e^{-i\xi_1}\end{pmatrix},$$ which is invertible because its determinant equals $e^{2i\psi}\neq 0$, and for $F\colon \mathrm{GL}_2(\mathbb{C})\to\mathbb{C}$ let $\mathrm{unitaryAverage}(F)$ be the scalar $\frac{1}{4\pi^3}$ times the iterated interval integral $\int_0^{2\pi}\!\int_0^{\pi/2}\!\int_0^{2\pi}\!\int_0^{2\pi}\sin\eta\cos\eta\,F(k(\psi,\eta,\xi_1,\xi_2))\,d\xi_2\,d\xi_1\,d\eta\,d\psi$. The assertion is: for every continuous $F\colon\mathrm{GL}_2(\mathbb{C})\to\mathbb{C}$, $\mathrm{unitaryAverage}(F)$ equals $\frac{1}{2\pi^3}$ times the Lebesgue integral, over the product set $\bigl((0,\pi)\times(0,\pi/2)\bigr)\times\bigl((0,2\pi)\times(0,2\pi)\bigr)$ of open intervals in $(\mathbb{R}\times\mathbb{R})\times(\mathbb{R}\times\mathbb{R})$, of the function sending $r=((\psi,\eta),(\xi_1,\xi_2))$ to $\sin\eta\cos\eta\,F(k(\psi,\eta,\xi_1,\xi_2))$. Thus the range of $\psi$ is halved to $(0,\pi)$ and the normalising constant doubled, and the four iterated interval integrals are replaced by a single integral over the open box.
--
--   This is the reconciliation of the iterated-integral definition of the normalised average over the unitary group in Hopf coordinates (Euler-angle type coordinates, in which $\psi\mapsto\psi+\pi$ acts trivially up to shifting $\xi_1,\xi_2$ by $\pi$) with a single Lebesgue integral over a box on which the coordinates are injective. It is used in the construction of orbital integrals on $\mathrm{GL}_2(\mathbb{C})$, being cited by [`AutomorphicForm.exists_pos_forall_isOrbitalIntegralOn_diagonal_complex_eq_mul_integral_unitaryAverage`](thm.html#AutomorphicForm.exists_pos_forall_isOrbitalIntegralOn_diagonal_complex_eq_mul_integral_unitaryAverage).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Twisted_unitaryAverage_eq_mul_setIntegral_of_continuous.lean

import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm.GL2Twisted

theorem AutomorphicForm.GL2Twisted.unitaryAverage_eq_mul_setIntegral_of_continuous
    (F : GL (Fin 2) ℂ → ℂ) (hF : Continuous F) :
    unitaryAverage F = (1 / (2 * Real.pi ^ 3) : ℂ) *
      ∫ r in (Set.Ioo 0 Real.pi ×ˢ Set.Ioo 0 (Real.pi / 2)) ×ˢ (Set.Ioo 0 (2 * Real.pi) ×ˢ Set.Ioo 0 (2 * Real.pi)),
        (Real.sin r.1.2 * Real.cos r.1.2 : ℂ) * F (unitaryElt r.1.1 r.1.2 r.2.1 r.2.2) := by sorry
