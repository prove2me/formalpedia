-- Prove2me | Theorems.Thm_BlackbodyRadiation_planckFreq_integrableOn_Ioi
-- name    : BlackbodyRadiation.planckFreq_integrableOn_Ioi
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T14:04:15.761304+00:00
-- url     : https://prove2.me/theorems/61eff190-f7a2-47b8-b30f-2116d7a6867c
-- title:
--   Finite total emission: $B_\nu$ is integrable on $(0,\infty)$
-- statement:
--   **Planck's law has a finite total emission.** For positive $h$, $c$, $k_B$ and $T$, the
--   Planck spectral radiance $B_\nu(\cdot,T)$ is Lebesgue integrable on $(0,\infty)$: the
--   quantization of the energy element removes the divergence that destroys the classical
--   prediction. Near $\nu=0$ the integrand behaves like $2\nu^2k_BT/c^2$ and near
--   $\nu=\infty$ it decays like $\nu^3e^{-h\nu/(k_BT)}$.
--
--   This is the side condition that gives the Stefan-Boltzmann law its meaning. In Lean the
--   Bochner integral of a non-integrable function is $0$ by definition, so an identity of the
--   form $\int_0^\infty \pi B_\nu\,d\nu = \sigma T^4$ asserts nothing about the physical total
--   emission until integrability is known independently.
-- source:
--   Planck constant, Wikipedia, https://en.wikipedia.org/wiki/Planck_constant , section "History", subsections "Origin of the constant" (Wien's law at short wavelengths, the Rayleigh-Jeans formula at long wavelengths, and Planck's spectral radiance per unit frequency) and "Development and application" (the ultraviolet catastrophe).

import Mathlib
import Definitions.Def_BlackbodyRadiation_planck
import Definitions.Def_BlackbodyRadiation_classical_limits
open MeasureTheory

namespace BlackbodyRadiation
theorem planckFreq_integrableOn_Ioi
    (h c kB T : ℝ) (hh : 0 < h) (hc : 0 < c) (hkB : 0 < kB) (hT : 0 < T) :
    IntegrableOn (fun ν : ℝ => planckFreq h c kB T ν) (Set.Ioi 0) volume := by sorry
end BlackbodyRadiation
