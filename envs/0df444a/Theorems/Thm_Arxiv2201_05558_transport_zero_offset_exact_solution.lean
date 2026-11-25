-- Prove2me | Theorems.Thm_Arxiv2201_05558_transport_zero_offset_exact_solution
-- name    : Arxiv2201_05558.transport_zero_offset_exact_solution
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T10:58:14.446025+00:00
-- url     : https://prove2.me/theorems/9ad7f172-4432-5c64-8bfe-94110cae6d9c
-- title:
--   Eq. (5.27): exact solution of the transport equation (5.14) at zero frequency offset
-- statement:
--   Let $\omega_0,c_o>0$ and let $C:\mathbb{R}^2\to\mathbb{R}$ be continuous, integrable and even, with integrable Fourier transform $\hat C(k)=\int C(x)e^{-ik\cdot x}dx$. Fix $\zeta\in\mathbb{R}^2$ and set $K(z)=(2\pi)^4e^{-\omega_0^2C(0)z/(4c_o^2)}$. Then the function
--
--   $$A(z,\xi,\zeta,0)=\frac{K(z)}{(2\pi)^2}\int_{\mathbb{R}^2}\Big[\exp\Big(\frac{\omega_0^2}{4c_o^2}\int_0^zC\big(x+\tfrac{c_o\zeta}{\omega_0}z'\big)dz'\Big)-1\Big]e^{-i\xi\cdot x}dx$$
--
--   satisfies $A(0,\xi,\zeta,0)=0$, and for every $z\ge0$ and $\xi$ it solves the transport equation (5.14) with $\Omega=0$:
--
--   $$\partial_zA=\frac{\omega_0^2}{4(2\pi)^2c_o^2}\int\hat C(k)\big[A(\xi-k)e^{\frac{ic_oz}{\omega_0}k\cdot\zeta}-A(\xi)\big]dk+\frac{\omega_0^2}{4(2\pi)^2c_o^2}K(z)\hat C(\xi)e^{\frac{ic_oz}{\omega_0}\xi\cdot\zeta}.$$
--
--   (5.14) describes the scattered part of the second moment in Proposition 5.1. At zero frequency offset it is solved in closed form.
--
--   **Formalization Note** The paper calls (5.27) "the" solution. The statement asserts that (5.27) is a solution, and does not assert uniqueness in a function class, which the paper does not specify. Continuity and integrability of $C$ and $\hat C$ are the paper's standing assumptions in Section 5.4 ($\hat C\in L^1$ is used in the proof of Proposition 5.1). Evenness follows from the definition (2.8) of $C$ and stationarity.
-- source:
--   Garnier and Sølna, Speckle Memory Effect in the Frequency Domain and Stability in Time-Reversal Experiments, arXiv:2201.05558v1 (2022), claim c054; Section 5.6, eq. (5.27) solving (5.13)-(5.14) of Proposition 5.1 with Ω = 0, PDF pp. 12, 17

import Mathlib
import Definitions.Def_Arxiv2201_05558_Basic

open MeasureTheory Filter Topology

namespace Arxiv2201_05558

theorem transport_zero_offset_exact_solution (ω0 c0 : ℝ) (hω0 : 0 < ω0) (hc0 : 0 < c0)
    (C : Plane → ℝ) (hCc : Continuous C) (hCi : Integrable C) (hCe : ∀ x, C (-x) = C x)
    (hCFi : Integrable (covFT C)) (ζ : Plane) :
    (∀ ξ, transportZero ω0 c0 C ζ 0 ξ = 0) ∧
    ∀ z : ℝ, 0 ≤ z → ∀ ξ : Plane,
      HasDerivAt (fun z' => transportZero ω0 c0 C ζ z' ξ)
        (transportRHS ω0 c0 C 0 ζ (transportZero ω0 c0 C ζ) z ξ) z := by sorry

end Arxiv2201_05558
