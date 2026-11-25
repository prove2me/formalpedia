-- Prove2me | Theorems.Thm_Arxiv2201_05558_hatAs_gaussian_solves_moment_equation
-- name    : Arxiv2201_05558.hatAs_gaussian_solves_moment_equation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T11:29:54.387536+00:00
-- url     : https://prove2.me/theorems/240aee19-18e4-511c-be83-961f54d5dc96
-- title:
--   Proposition 5.4 (as proved): the explicit complex Gaussian $\hat A_s$ solves the reduced moment equation
-- statement:
--   Let $\omega_0,c_o,D>0$, $\Omega\ne0$ and $\zeta\in\mathbb{R}^2$. Let $a_\Omega,b_\Omega,c_\Omega,d_\Omega$ be given by (5.39)-(5.46) with $s=\sqrt{D\Omega/(4c_o)}\,z$, where
--
--   $$\Psi_a(s)=\ln\cosh(e^{-i\pi/4}s),\qquad\Psi_b(s)=\frac{\tanh(e^{-i\pi/4}s)}{e^{-i\pi/4}s},\qquad \Psi_c(s)=2i\frac{e^{-i\pi/4}s\tanh(e^{-i\pi/4}s)-1+\cosh(e^{-i\pi/4}s)^{-1}}{s^2},$$
--
--   $$\Psi_d(s)=1-\frac{3i}{s^3}\int_0^s\big(e^{-i\pi/4}s'\tanh(e^{-i\pi/4}s')-1+\cosh(e^{-i\pi/4}s')^{-1}\big)^2ds'$$
--
--   (for $\Omega<0$, the complex conjugates of the coefficients at $-\Omega$). Then the complex Gaussian
--
--   $$\hat A_s(z,x,\zeta,\Omega)=(2\pi)^2\exp\big[-a_\Omega(z)-b_\Omega(z)|x|^2-c_\Omega(z)\,x\cdot\zeta-d_\Omega(z)|\zeta|^2\big]$$
--
--   satisfies, for all $z>0$ and $x\in\mathbb{R}^2$,
--
--   $$\partial_z\hat A_s=-\frac{ic_o\Omega}{\omega_0^2}\Delta_x\hat A_s-\frac{\omega_0^2D}{16c_o^2}\Big[|x|^2+\frac{z^2c_o^2}{\omega_0^2}|\zeta|^2+2\frac{zc_o}{\omega_0}\zeta\cdot x\Big]\hat A_s,$$
--
--   and $\hat A_s(z,x,\zeta,\Omega)\to(2\pi)^2$ as $z\to0^+$.
--
--   This equation is the partial inverse Fourier transform in $\xi$ of the parabolic equation (5.33) of Proposition 5.3, with initial value $(2\pi)^4\delta(\xi)$. Its solution gives explicit second- and fourth-order moments of the Green's function in the strongly scattering regime.
--
--   **Formalization Note** The paper states that the partial inverse Fourier transform of the solution $A_s$ of (5.33) has this form. Its proof passes to the equation above for $\hat A_s$ and verifies that the Gaussian solves it. The Lean statement is that verification: $A_s$ has a Dirac initial value and is not defined in Lean, and uniqueness in an unspecified class is not asserted. $\Omega=0$ is excluded because the formulas are undefined there ($s=0$).
-- source:
--   Garnier and Sølna, Speckle Memory Effect in the Frequency Domain and Stability in Time-Reversal Experiments, arXiv:2201.05558v1 (2022), claim c056; Section 5.6, Proposition 5.4, eqs. (5.38)-(5.46), and the equation for $\hat A_s$ in its proof, PDF pp. 20-21

import Mathlib
import Definitions.Def_Arxiv2201_05558_Basic

open MeasureTheory Filter Topology

namespace Arxiv2201_05558

theorem hatAs_gaussian_solves_moment_equation (ω0 c0 D Ω : ℝ) (hω0 : 0 < ω0) (hc0 : 0 < c0)
    (hD : 0 < D) (hΩ : Ω ≠ 0) (ζ : Plane) :
    SolvesMomentEq ω0 c0 D Ω ζ (hatAs ω0 c0 D (fun _ => 0) Ω ζ)
      (fun _ => ((2 * Real.pi : ℝ) : ℂ) ^ 2) := by sorry

end Arxiv2201_05558
