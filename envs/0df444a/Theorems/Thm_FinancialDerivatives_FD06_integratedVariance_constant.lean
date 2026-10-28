-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_integratedVariance_constant
-- name    : FinancialDerivatives.FD06.integratedVariance_constant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:36:37.259523+00:00
-- url     : https://prove2.me/theorems/908b7932-39fa-4f92-b148-57d802c7f563
-- title:
--   Integrated constant volatility
-- statement:
--   Integrated constant volatility
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_integratedVariance

namespace FinancialDerivatives.FD06

theorem integratedVariance_constant (σ t T : ℝ) : integratedVariance (fun _ => σ) t T = σ ^ 2 * (T - t) := by sorry

end FinancialDerivatives.FD06
