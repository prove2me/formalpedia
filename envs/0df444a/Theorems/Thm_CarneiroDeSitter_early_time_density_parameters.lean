-- Prove2me | Theorems.Thm_CarneiroDeSitter_early_time_density_parameters
-- name    : CarneiroDeSitter.early_time_density_parameters
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T02:17:50.803241+00:00
-- url     : https://prove2.me/theorems/9919c3f4-85e3-473c-8e79-ceb6ff43fcba
-- title:
--   p. 2245: $\Omega_m=1-H^2$, $\Omega_\Lambda=H^2$, $q=1-2H^2$ in the early universe
-- statement:
--   Let $H,\rho_T,\rho_m,\Lambda:\mathbb R\to\mathbb R$ satisfy, for all $s$, $\rho_T(s)=3H(s)^2$, $\Lambda(s)=3H(s)^4$ and $\rho_T(s)=\rho_m(s)+\Lambda(s)$. Let $t$ be a time with $H(t)\neq0$ at which $H$ solves the evolution equation (12), $\dot H(t)=-2H(t)^2+2H(t)^4$. Then
--
--   1. $\Omega_m(t)=\rho_m(t)/\rho_T(t)=1-H(t)^2$;
--   2. $\Omega_\Lambda(t)=\Lambda(t)/\rho_T(t)=H(t)^2$;
--   3. the deceleration parameter $q(t)=-1-\dot H(t)/H(t)^2$ equals $1-2H(t)^2$.
--
--   These identities describe the phase transition: as $H$ falls from $1$ to $0$, $\Omega_m$ goes from $0$ to $1$ and $q$ from $-1$ to $1$.
-- source:
--   S. Carneiro, "From de Sitter to de Sitter: a non-singular inflationary universe driven by vacuum", Int. J. Mod. Phys. D 15 (2006) 2241-2247, https://doi.org/10.1142/S0218271806009510, p. 2245, first paragraph (relative energy densities and deceleration factor); Figs. 2, 3

import Mathlib
import Definitions.Def_CarneiroDeSitter2006

open Real Filter Topology Asymptotics MeasureTheory Set

namespace CarneiroDeSitter

theorem early_time_density_parameters (H ρT ρm Λ : ℝ → ℝ) (t : ℝ)
    (hFriedmann : ∀ s, ρT s = 3 * H s ^ 2)
    (hVacuum : ∀ s, Λ s = 3 * H s ^ 4)
    (hSplit : ∀ s, ρT s = ρm s + Λ s)
    (hode : HasDerivAt H (-2 * H t ^ 2 + 2 * H t ^ 4) t)
    (hH : H t ≠ 0) :
    ρm t / ρT t = 1 - H t ^ 2 ∧ Λ t / ρT t = H t ^ 2 ∧
    decelerationParameter H t = 1 - 2 * H t ^ 2 := by sorry

end CarneiroDeSitter
