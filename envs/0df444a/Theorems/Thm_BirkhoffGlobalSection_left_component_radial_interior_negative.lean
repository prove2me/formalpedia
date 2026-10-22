-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_left_component_radial_interior_negative
-- name    : BirkhoffGlobalSection.left_component_radial_interior_negative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T10:10:56.179972+00:00
-- url     : https://prove2.me/theorems/63d43337-c6c2-4eef-9dd5-3e42b92d50e1
-- title:
--   Strict negativity inside each ray of the left energy boundary
-- statement:
--   Suppose the positive ray $R x$ meets the selected subcritical regularized energy component, with $x$ a unit phase vector and $R>0$. At every strictly smaller positive radius $0<r<R$ along the same ray, the regularized Hamiltonian is strictly negative: $K_{\mu,c}(rx)<0$. This strict radial sublevel property rules out a second intersection of that ray with the zero-energy component.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4, radial star-shapedness of the regularized component.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem left_component_radial_interior_negative (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ x ∈ unitThreeSphere, ∀ R : ℝ,
      0 < R → (fun i : Fin 4 => R * x i) ∈ leftEnergyComponent μ c →
      ∀ r : ℝ, 0 < r → r < R →
        leviCivitaHamiltonian μ c (fun i : Fin 4 => r * x i) < 0 := by sorry

end BirkhoffGlobalSection
