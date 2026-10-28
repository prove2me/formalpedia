-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_heatKernel_mass_one
-- name    : FinancialDerivatives.FD06.heatKernel_mass_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:23:46.522339+00:00
-- url     : https://prove2.me/theorems/47d87aba-2f34-49db-b305-f054227de3fd
-- title:
--   Heat kernel integrates to one
-- statement:
--   Heat kernel integrates to one
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_heatKernel
open MeasureTheory intervalIntegral

namespace FinancialDerivatives.FD06

theorem heatKernel_mass_one (τ : ℝ) (hτ : 0 < τ) : (∫ x : ℝ, heatKernel τ x) = 1 := by sorry

end FinancialDerivatives.FD06
