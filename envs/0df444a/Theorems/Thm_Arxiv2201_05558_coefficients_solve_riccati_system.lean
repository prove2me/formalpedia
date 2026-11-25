-- Prove2me | Theorems.Thm_Arxiv2201_05558_coefficients_solve_riccati_system
-- name    : Arxiv2201_05558.coefficients_solve_riccati_system
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T11:03:43.668801+00:00
-- url     : https://prove2.me/theorems/6d176ec6-7f36-4e59-9b25-fd948525d64b
-- title:
--   Proposition 5.4 (proof, eqs. (5.47)-(5.50)): the coefficients solve the Riccati system
-- statement:
--   Let $\omega_0,c_o,D>0$ and $\Omega\ne0$. Define $a_\Omega,b_\Omega,c_\Omega,d_\Omega$ by (5.39)-(5.46) for $\Omega>0$, and by complex conjugation of the coefficients at $-\Omega$ for $\Omega<0$. Then on $z>0$
--
--   $$\frac{da_\Omega}{dz}=-i\frac{4c_o\Omega}{\omega_0^2}b_\Omega,\qquad \frac{db_\Omega}{dz}=\frac{\omega_0^2D}{16c_o^2}+i\frac{4c_o\Omega}{\omega_0^2}b_\Omega^2,$$
--
--   $$\frac{dc_\Omega}{dz}=\frac{\omega_0Dz}{8c_o}+i\frac{4c_o\Omega}{\omega_0^2}b_\Omega c_\Omega,\qquad \frac{dd_\Omega}{dz}=\frac{Dz^2}{16}+i\frac{c_o\Omega}{\omega_0^2}c_\Omega^2,$$
--
--   and all four coefficients tend to $0$ as $z\to0^+$.
--
--   This is the system (5.47)-(5.50) with zero initial data, which the proof of Proposition 5.4 solves to obtain the explicit coefficients.
--
--   **Formalization Note** The zero initial data are stated as limits as $z\to0^+$, because the formulas involve $\Psi_{b,c,d}(s)$, which are undefined at $s=0$. The case $\Omega=0$, where $s=0$ for every $z$, is excluded for the same reason. $\Psi_a$ is the continuous determination of $\ln\cosh$ (see the definitions).
-- source:
--   Garnier and Sølna, Speckle Memory Effect in the Frequency Domain and Stability in Time-Reversal Experiments, arXiv:2201.05558v1 (2022), claim c056; Section 5.6, proof of Proposition 5.4, eqs. (5.39)-(5.50), PDF pp. 20-21

import Mathlib
import Definitions.Def_Arxiv2201_05558_Basic

open MeasureTheory Filter Topology

namespace Arxiv2201_05558

theorem coefficients_solve_riccati_system (ω0 c0 D Ω : ℝ) (hω0 : 0 < ω0) (hc0 : 0 < c0)
    (hD : 0 < D) (hΩ : Ω ≠ 0) :
    SolvesCoefODE ω0 c0 D Ω (aOm c0 D (fun _ => 0) Ω) (bOm ω0 c0 D (fun _ => 0) Ω)
      (cOm ω0 c0 D (fun _ => 0) Ω) (dOm c0 D (fun _ => 0) Ω) ∧
    Tendsto (aOm c0 D (fun _ => 0) Ω) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (bOm ω0 c0 D (fun _ => 0) Ω) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (cOm ω0 c0 D (fun _ => 0) Ω) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (dOm c0 D (fun _ => 0) Ω) (𝓝[>] 0) (𝓝 0) := by sorry

end Arxiv2201_05558
