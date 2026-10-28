-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_integratedVariance_nonneg
-- name    : FinancialDerivatives.FD06.integratedVariance_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:35:19.716658+00:00
-- url     : https://prove2.me/theorems/bb0f4b86-fedb-4089-8322-050e712711b4
-- title:
--   Nonnegative integrated variance
-- statement:
--   Nonnegative integrated variance
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_integratedVariance

namespace FinancialDerivatives.FD06

theorem integratedVariance_nonneg (σ : ℝ → ℝ) (t T : ℝ) (h : t ≤ T) : 0 ≤ integratedVariance σ t T := by sorry

end FinancialDerivatives.FD06
