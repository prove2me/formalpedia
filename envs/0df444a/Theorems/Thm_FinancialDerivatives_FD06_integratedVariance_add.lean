-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_integratedVariance_add
-- name    : FinancialDerivatives.FD06.integratedVariance_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:34:49.175807+00:00
-- url     : https://prove2.me/theorems/20be2005-642c-404d-84ad-d573e269333e
-- title:
--   Additive integrated variance
-- statement:
--   Additive integrated variance
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_integratedVariance

namespace FinancialDerivatives.FD06

theorem integratedVariance_add (σ : ℝ → ℝ) (t u T : ℝ) (hσ : Continuous σ) : integratedVariance σ t T = integratedVariance σ t u + integratedVariance σ u T := by sorry

end FinancialDerivatives.FD06
