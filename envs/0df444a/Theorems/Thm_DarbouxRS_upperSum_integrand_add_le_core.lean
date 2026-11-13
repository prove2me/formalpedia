-- Prove2me | Theorems.Thm_DarbouxRS_upperSum_integrand_add_le_core
-- name    : DarbouxRS.upperSum_integrand_add_le_core
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T15:32:44.377108+00:00
-- url     : https://prove2.me/theorems/2e366b22-5b10-4735-8b96-308937b0f2c7
-- title:
--   Chapter 1, thm_1_2: DarbouxRS.upperSum_integrand_add_le_core
-- statement:
--   Source theorem `DarbouxRS.upperSum_integrand_add_le_core` from Chapter 1, module `thm_1_2`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic

open scoped BigOperators Pointwise

open Finset Set

noncomputable section Thm_1_2

namespace DarbouxRS

theorem upperSum_integrand_add_le_core {a b : ℝ} (P : Partition a b)
    {f g alpha : ℝ → ℝ}
    (hsf : SourceHypotheses a b f alpha)
    (hsg : SourceHypotheses a b g alpha) :
    upperSum P (fun x => f x + g x) alpha ≤
      upperSum P f alpha + upperSum P g alpha := by sorry

end DarbouxRS

end Thm_1_2

noncomputable section Darboux_fundamental_result

namespace Refinement

end Refinement

namespace Partition

end Partition

end Darboux_fundamental_result
