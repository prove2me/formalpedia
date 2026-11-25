-- Prove2me | Theorems.Thm_Arxiv2201_05558_zero_offset_coefficients_revisited
-- name    : Arxiv2201_05558.zero_offset_coefficients_revisited
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T11:41:56.65613+00:00
-- url     : https://prove2.me/theorems/4439e03f-84fe-5321-82cc-cd1063f71a9d
-- title:
--   Eq. (5.62): the coefficients at zero frequency offset in the revised scintillation regime
-- statement:
--   Let $\omega_0,c_o,\rho_0>0$ and $D\in\mathbb{R}$. Let $a,b,c,d:(0,\infty)\to\mathbb{C}$ solve the system (5.47)-(5.50) with $\Omega=0$ on $z>0$:
--
--   $$a'=0,\qquad b'=\frac{\omega_0^2D}{16c_o^2},\qquad c'=\frac{\omega_0Dz}{8c_o},\qquad d'=\frac{Dz^2}{16}.$$
--
--   Take the initial values of the proof of Proposition 5.7, $(a,b,c,d)\to(0,\frac1{4\rho_0^2},0,0)$ as $z\to0^+$. Then for every $z>0$
--
--   $$a_0(z)=0,\qquad b_0(z)=\frac{\omega_0^2Dz}{16c_o^2}+\frac1{4\rho_0^2},\qquad c_0(z)=\frac{\omega_0Dz^2}{16c_o},\qquad d_0(z)=\frac{Dz^3}{48}.$$
--
--   **Formalization Note** The paper prints the third coefficient as "$c_o(z)$"; it is $c_0(z)$, the coefficient $c_\Omega$ at $\Omega=0$, not the wave speed. Initial values are stated as right limits at $0$.
-- source:
--   Garnier and Sølna, Speckle Memory Effect in the Frequency Domain and Stability in Time-Reversal Experiments, arXiv:2201.05558v1 (2022), claim c018; Section 5.7, eq. (5.62), with the system (5.47)-(5.50) and $b_\Omega(0) = 1/(4\rho_0^2)$ from the proof of Proposition 5.7, PDF p. 24

import Mathlib
import Definitions.Def_Arxiv2201_05558_Basic

open MeasureTheory Filter Topology

namespace Arxiv2201_05558

theorem zero_offset_coefficients_revisited (ω0 c0 D ρ0 : ℝ) (hω0 : 0 < ω0) (hc0 : 0 < c0)
    (hρ0 : 0 < ρ0) (a b c d : ℝ → ℂ) (hode : SolvesCoefODE ω0 c0 D 0 a b c d)
    (ha : Tendsto a (𝓝[>] 0) (𝓝 0))
    (hb : Tendsto b (𝓝[>] 0) (𝓝 ((1 / (4 * ρ0 ^ 2) : ℝ) : ℂ)))
    (hc : Tendsto c (𝓝[>] 0) (𝓝 0)) (hd : Tendsto d (𝓝[>] 0) (𝓝 0)) :
    ∀ z : ℝ, 0 < z → a z = 0 ∧
      b z = ((ω0 ^ 2 * D * z / (16 * c0 ^ 2) + 1 / (4 * ρ0 ^ 2) : ℝ) : ℂ) ∧
      c z = ((ω0 * D * z ^ 2 / (16 * c0) : ℝ) : ℂ) ∧
      d z = ((D * z ^ 3 / 48 : ℝ) : ℂ) := by sorry

end Arxiv2201_05558
