-- Prove2me | Theorems.Thm_DarkEnergyLCDM_no_acceleration_without_lambda
-- name    : DarkEnergyLCDM.no_acceleration_without_lambda
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T01:04:19.654461+00:00
-- url     : https://prove2.me/theorems/967a42e9-18d7-46a6-bf8e-63f1fd0ef902
-- title:
--   No acceleration without $\Lambda$ for $\rho,p\ge0$
-- statement:
--   Let $G>0$, and let $t$ be an instant with $a(t)>0$, $\rho(t)\ge 0$ and $p(t)\ge0$. Suppose the acceleration equation (7) holds at $t$ with $\Lambda = 0$. Then
--   $$\ddot a(t) \le 0.$$
--
--   This is the observation, made after Eq. (7), that without a cosmological constant positive acceleration is impossible because $\rho$ and $p$ are non-negative.
-- source:
--   R. von Marttens, J. Alcaniz, S. Carneiro, "A energia escura e os desafios do modelo cosmológico padrão", Cadernos de Astronomia 7(1), 62–76 (2026), https://doi.org/10.47456/Cad.Astro.v7n1.52249, p. 65, text between Eqs. (7) and (8)

import Mathlib
import Definitions.Def_DarkEnergyLCDM_Defs

namespace DarkEnergyLCDM

theorem no_acceleration_without_lambda (G : ℝ) (hG : 0 < G) (a ρ p : ℝ → ℝ) (t : ℝ)
    (ha : 0 < a t) (hρ : 0 ≤ ρ t) (hp : 0 ≤ p t)
    (hacc : AccelerationEq G 0 a ρ p t) :
    deriv (deriv a) t ≤ 0 := by sorry

end DarkEnergyLCDM
