-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_component_closure_energy_zero
-- name    : BirkhoffGlobalSection.left_component_closure_energy_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-23T18:29:48.28852+00:00
-- url     : https://prove2.me/theorems/e453a326-6bcf-4d05-b31a-8b48bf876211
-- title:
--   Energy equation holds on the closure of the left component
-- statement:
--   For $0<\mu<1$ and energy $-c$ below the first critical value, every limit point of the selected component satisfies the zero equation for the Levi-Civita Hamiltonian. The Hamiltonian is continuous away from the excluded second collision, so the energy equation passes to such limits.
-- source:
--   Joung--van Koert, Proposition 2.4 and its proof, https://arxiv.org/abs/2407.19159v3, PDF p. 7.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- On the closure of the selected component, the regularized energy equation
still holds; collision exclusion allows continuity of the Hamiltonian there. -/
theorem left_component_closure_energy_zero (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ s ∈ closure (leftEnergyComponent μ c),
      leviCivitaHamiltonian μ c s = 0 := by sorry

end BirkhoffGlobalSection
