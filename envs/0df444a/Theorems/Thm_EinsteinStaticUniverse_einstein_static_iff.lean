-- Prove2me | Theorems.Thm_EinsteinStaticUniverse_einstein_static_iff
-- name    : EinsteinStaticUniverse.einstein_static_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T04:24:34.953763+00:00
-- url     : https://prove2.me/theorems/583464e2-2f4f-43ec-8d83-6db8afab2382
-- title:
--   The Einstein static universe: $\Lambda=4\pi G\rho_E$ and $k=\Lambda a_E^2$
-- statement:
--   Einstein's 1917 model is the requirement that the universe neither expands nor contracts. Let $G,\Lambda,k,\rho_0,a_0$ be real parameters and let $a_E>0$. The constant scale factor $a\equiv a_E$ satisfies both Friedmann equations at all times if and only if
--   $$\Lambda=4\pi G\,\rho_E\qquad\text{and}\qquad k=\Lambda\,a_E^{2},\qquad \rho_E:=\rho_0\left(\frac{a_0}{a_E}\right)^{3}.$$
--
--   In words: a static universe filled with dust of density $\rho_E$ exists exactly when the cosmological constant is tuned to $4\pi G\rho_E$ and the spatial curvature is tuned to $\Lambda a_E^{2}$. For positive $G,\rho_0,a_0$ both constants are then positive, so the Einstein static universe is necessarily closed ($k>0$) and has $\Lambda>0$; there is no static balance with $\Lambda=0$ and dust present.
--
--   This is the source of the fine-tuning objection to the static model: the balance holds for one relation among the parameters and for no other.
-- source:
--   Wikipedia, 'Cosmological constant', https://en.wikipedia.org/wiki/Cosmological_constant (sections 'History', 'Equation', 'Density parameter', 'Equation of state', 'Value', 'Predictions'); Wikipedia, 'Cosmological constant problem', https://en.wikipedia.org/wiki/Cosmological_constant_problem (sections 'History', 'Estimated values')

import Mathlib
import Definitions.Def_EinsteinStaticUniverse_model

namespace EinsteinStaticUniverse

theorem einstein_static_iff (G Λ k ρ₀ a₀ aE : ℝ) (haE : 0 < aE) :
    (FriedmannI G Λ k ρ₀ a₀ (fun _ => aE) Set.univ ∧
        FriedmannII G Λ ρ₀ a₀ (fun _ => aE) Set.univ) ↔
      (Λ = 4 * Real.pi * G * dustDensity ρ₀ a₀ aE ∧ k = Λ * aE ^ 2) := by sorry

end EinsteinStaticUniverse
