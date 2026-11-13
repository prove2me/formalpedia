-- Prove2me | Theorems.Thm_DarbouxRS_lowerSum_integrand_add_le_core
-- name    : DarbouxRS.lowerSum_integrand_add_le_core
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:46:37.106552+00:00
-- url     : https://prove2.me/theorems/362e3c6a-0998-48e7-99b3-9bba2cc5bcce
-- title:
--   Source theorem: DarbouxRS.lowerSum_integrand_add_le_core
-- statement:
--   Original source theorem extracted from ProbabilityTheory.chapter_01.thm_1_2. Type preserved exactly.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic
open scoped BigOperators Pointwise
open Finset Set
noncomputable section Thm_1_2
namespace DarbouxRS

theorem lowerSum_integrand_add_le_core {a b : ℝ} (P : Partition a b)
    {f g alpha : ℝ → ℝ}
    (hsf : SourceHypotheses a b f alpha)
    (hsg : SourceHypotheses a b g alpha) :
    lowerSum P f alpha + lowerSum P g alpha ≤
      lowerSum P (fun x => f x + g x) alpha := by
  sorry
end DarbouxRS
end Thm_1_2
