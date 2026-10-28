-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_heatKernel_semigroup
-- name    : FinancialDerivatives.FD06.heatKernel_semigroup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:24:11.831613+00:00
-- url     : https://prove2.me/theorems/03d16802-7f9d-4544-b280-ecd9e97694f4
-- title:
--   Gaussian heat semigroup convolution identity
-- statement:
--   Gaussian heat semigroup convolution identity
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_heatKernel
open MeasureTheory intervalIntegral

namespace FinancialDerivatives.FD06

theorem heatKernel_semigroup (s t x : ℝ) (hs : 0 < s) (ht : 0 < t) : (∫ y : ℝ, heatKernel s (x - y) * heatKernel t y) = heatKernel (s + t) x := by sorry

end FinancialDerivatives.FD06
