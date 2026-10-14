-- Prove2me | Theorems.Thm_ActuarialFoundations_fa_R_weighted
-- name    : ActuarialFoundations.fa_R_weighted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T23:34:18.557956+00:00
-- url     : https://prove2.me/theorems/63bf3e3f-9b04-4d8c-9528-bd2ce92bfcf3
-- title:
--   R weighted
-- statement:
--   Prove the closed finite double-sum increasing-benefit weighting for the stated exact Lean assumptions, directly from the life-table and cashflow definitions. The claim is valued at the end of the death year, and terminal-age endpoints are disjoint. No commutation equivalence or desired result may be inserted as a hypothesis.
-- source:
--   Institute of Actuaries (1971), International Actuarial Notation, commutation functions, p.50, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf. Original derived theorem; not a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faDiscountedDeaths
import Definitions.Def_actuarial_faR

namespace ActuarialFoundations

theorem fa_R_weighted (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) : faR l v ω x = (∑ k ∈ Finset.range (ω-x), ((k+1 : ℕ) : ℝ) * faDiscountedDeaths l v (x+k)) := by sorry

end ActuarialFoundations
