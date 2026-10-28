-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_heatFlow_solves_heat_equation
-- name    : FinancialDerivatives.FD06.heatFlow_solves_heat_equation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:25:31.220095+00:00
-- url     : https://prove2.me/theorems/9fad3fbe-b671-4669-973b-197366820147
-- title:
--   Classical heat-flow PDE
-- statement:
--   Classical heat-flow PDE
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_gaussianHeatFlow

namespace FinancialDerivatives.FD06

theorem heatFlow_solves_heat_equation (f : ℝ → ℝ) (M : ℝ) (hf : ContDiff ℝ 2 f) (hb : ∀ x, |f x| ≤ M) (τ x : ℝ) (hτ : 0 < τ) : deriv (fun u => gaussianHeatFlow f u x) τ = deriv (deriv (fun y => gaussianHeatFlow f τ y)) x := by sorry

end FinancialDerivatives.FD06
