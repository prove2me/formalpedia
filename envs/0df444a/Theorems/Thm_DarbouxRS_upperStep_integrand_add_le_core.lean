-- Prove2me | Theorems.Thm_DarbouxRS_upperStep_integrand_add_le_core
-- name    : DarbouxRS.upperStep_integrand_add_le_core
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T15:31:21.463435+00:00
-- url     : https://prove2.me/theorems/2462584e-4c83-4c5d-971f-78a1d8759e04
-- title:
--   Chapter 1, thm_1_2: DarbouxRS.upperStep_integrand_add_le_core
-- statement:
--   Source theorem `DarbouxRS.upperStep_integrand_add_le_core` from Chapter 1, module `thm_1_2`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Mathlib.Tactic

open scoped BigOperators Pointwise

open Finset Set

noncomputable section Thm_1_2

namespace DarbouxRS

theorem upperStep_integrand_add_le_core {a b : ℝ}
    {f g : ℝ → ℝ}
    (P : Partition a b)
    (i : Fin P.n)
    (hfAbove : BddAbove (f '' Set.Icc a b))
    (hgAbove : BddAbove (g '' Set.Icc a b)) :
    upperStep P (fun x => f x + g x) i ≤ upperStep P f i + upperStep P g i := by sorry

end DarbouxRS

end Thm_1_2

noncomputable section Darboux_fundamental_result

namespace Refinement

end Refinement

namespace Partition

end Partition

end Darboux_fundamental_result
