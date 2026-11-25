-- Prove2me | Theorems.Thm_Arxiv2201_05558_hatAs_revisited_solves_moment_equation
-- name    : Arxiv2201_05558.hatAs_revisited_solves_moment_equation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T11:36:09.288074+00:00
-- url     : https://prove2.me/theorems/dfdda10e-7f9f-5abb-9b25-512becc41195
-- title:
--   Proposition 5.7 (as proved): the complex Gaussian $\hat A_s$ with $T_0$ solves the reduced moment equation
-- statement:
--   Let $\omega_0,c_o,D,\rho_0>0$, $\Omega\ne0$ and $\zeta\in\mathbb{R}^2$. Let $T_0=\frac{2e^{-i\pi/4}}{\omega_0^2\rho_0^2}\sqrt{\frac{c_o^3\Omega}{D}}$. Let $a_\Omega,b_\Omega,c_\Omega,d_\Omega$ be given by (5.39)-(5.42) with the functions
--
--   $$\Psi_a(s)=\ln[\cosh(ws)+T_0\sinh(ws)],\qquad \Psi_b(s)=\frac{T_0+\tanh(ws)}{ws[1+T_0\tanh(ws)]},$$
--
--   $$\Psi_c(s)=2i\frac{ws\frac{T_0+\tanh(ws)}{1+T_0\tanh(ws)}-1+[\cosh(ws)+T_0\sinh(ws)]^{-1}}{s^2},\qquad \Psi_d(s)=1-\frac{3i}{s^3}\int_0^s\Big(ws'\frac{T_0+\tanh(ws')}{1+T_0\tanh(ws')}-1+[\cosh(ws')+T_0\sinh(ws')]^{-1}\Big)^2ds',$$
--
--   where $w=e^{-i\pi/4}$. For $\Omega<0$, take the complex conjugates of the coefficients at $-\Omega$. Then $\hat A_s(z,x,\zeta,\Omega)=(2\pi)^2\exp[-a_\Omega(z)-b_\Omega(z)|x|^2-c_\Omega(z)x\cdot\zeta-d_\Omega(z)|\zeta|^2]$ satisfies, for all $z>0$ and $x$,
--
--   $$\partial_z\hat A_s=-\frac{ic_o\Omega}{\omega_0^2}\Delta_x\hat A_s-\frac{\omega_0^2D}{16c_o^2}\Big[|x|^2+\frac{z^2c_o^2}{\omega_0^2}|\zeta|^2+2\frac{zc_o}{\omega_0}\zeta\cdot x\Big]\hat A_s,$$
--
--   and $\hat A_s(z,x,\zeta,\Omega)\to(2\pi)^2e^{-|x|^2/(4\rho_0^2)}$ as $z\to0^+$. This initial value is the partial inverse Fourier transform of $(2\pi)^4\phi^1_{\sqrt2\rho_0}$.
--
--   This is the strongly scattering moment in the scintillation regime (5.51), where the mirror elements are comparable to the correlation length of the medium.
--
--   **Formalization Note** As for Proposition 5.4, the statement is the verification carried out in the proof: the same equation, with initial condition $b_\Omega(0)=1/(4\rho_0^2)$. The conjugation rule for $\Omega<0$ is the one stated in the proof of Proposition 5.4, applied to the same system (5.47)-(5.50), which has real initial data. $\Omega=0$ is excluded because $s=0$ and $T_0=0$ make the formulas undefined; that case is eq. (5.62).
-- source:
--   Garnier and Sølna, Speckle Memory Effect in the Frequency Domain and Stability in Time-Reversal Experiments, arXiv:2201.05558v1 (2022), claim c059; Section 5.7, Proposition 5.7, eqs. (5.57)-(5.61), and its proof, PDF pp. 23-24

import Mathlib
import Definitions.Def_Arxiv2201_05558_Basic

open MeasureTheory Filter Topology

namespace Arxiv2201_05558

theorem hatAs_revisited_solves_moment_equation (ω0 c0 D ρ0 Ω : ℝ) (hω0 : 0 < ω0)
    (hc0 : 0 < c0) (hD : 0 < D) (hρ0 : 0 < ρ0) (hΩ : Ω ≠ 0) (ζ : Plane) :
    SolvesMomentEq ω0 c0 D Ω ζ (hatAs ω0 c0 D (T0 ω0 c0 D ρ0) Ω ζ)
      (fun x => ((2 * Real.pi : ℝ) : ℂ) ^ 2 * (Real.exp (-‖x‖ ^ 2 / (4 * ρ0 ^ 2)) : ℂ)) := by sorry

end Arxiv2201_05558
