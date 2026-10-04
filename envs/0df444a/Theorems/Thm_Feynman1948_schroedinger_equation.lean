-- Prove2me | Theorems.Thm_Feynman1948_schroedinger_equation
-- name    : Feynman1948.schroedinger_equation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T18:17:43.978128+00:00
-- url     : https://prove2.me/theorems/b211e250-3bac-4805-b773-d00c7f6299c0
-- title:
--   Eq. (30): the path-integral wave function satisfies Schrödinger's equation
-- statement:
--   Section 6 of Feynman (1948): for a particle of mass $m>0$ moving in one dimension in a potential $V$, with the short-time action (22) and the normalization $A=(2\pi\hbar\varepsilon i/m)^{1/2}$ of (28), the relation (18)/(23)
--   $$\psi(x,t+\varepsilon)=\frac1A\int\exp\!\Big[\frac{i\varepsilon}{\hbar}\Big\{\frac m2\Big(\frac{x-y}{\varepsilon}\Big)^2-V(x)\Big\}\Big]\psi(y,t)\,dy$$
--   holding to first order in $\varepsilon$ gives Schrödinger's equation (30),
--   $$-\frac{\hbar}{i}\frac{\partial\psi}{\partial t}=\frac{1}{2m}\Big(\frac{\hbar}{i}\frac{\partial}{\partial x}\Big)^2\psi+V(x)\psi .$$
--   Formalized statement: for every Schwartz function $\psi$ (smooth and rapidly decreasing) and every $x$, the time-difference quotient of one path-integral step converges to the Schrödinger time derivative:
--   $$\lim_{\varepsilon\to0^+}\frac{(U_\varepsilon\psi)(x)-\psi(x)}{\varepsilon} = -\frac{i}{\hbar}\Big(-\frac{\hbar^2}{2m}\psi''(x)+V(x)\psi(x)\Big).$$
--   Equivalently, the generator of the path-integral evolution is $-\frac{i}{\hbar}H$ with $H=-\frac{\hbar^2}{2m}\partial_x^2+V$.
-- source:
--   R. P. Feynman, Space-Time Approach to Non-Relativistic Quantum Mechanics, Rev. Mod. Phys. 20, 367 (1948), https://doi.org/10.1103/RevModPhys.20.367, pp. 374-376, Section 6, Eqs. (18), (22), (23), (28)-(30)

import Mathlib
import Definitions.Def_Feynman1948_WaveEquation

open Complex Filter Topology SchwartzMap

namespace Feynman1948

theorem schroedinger_equation (ħ m : ℝ) (hħ : 0 < ħ) (hm : 0 < m) (V : ℝ → ℝ)
    (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Tendsto (fun ε : ℝ => (stepEvolution ħ m V ε ψ x - ψ x) / ε) (𝓝[>] 0)
      (𝓝 (-(I / ħ) * hamiltonian ħ m V ψ x)) := by sorry

end Feynman1948
