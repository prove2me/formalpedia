-- Prove2me | Theorems.Thm_ActuarialFoundations_fa_R_recursion
-- name    : ActuarialFoundations.fa_R_recursion
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T23:32:34.409996+00:00
-- url     : https://prove2.me/theorems/25a2bcc2-e289-4527-9662-5ef1da24eb23
-- title:
--   R recursion
-- statement:
--   Prove the exact one-year backward commutation recurrence for the stated exact Lean assumptions, directly from the life-table and cashflow definitions. The claim is valued at the end of the death year, and terminal-age endpoints are disjoint. No commutation equivalence or desired result may be inserted as a hypothesis.
-- source:
--   Institute of Actuaries (1971), International Actuarial Notation, commutation functions, p.50, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf. Original derived theorem; not a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faM
import Definitions.Def_actuarial_faR

namespace ActuarialFoundations

theorem fa_R_recursion (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) (hx : x < ω) : faR l v ω x = faM l v ω x + faR l v ω (x+1) := by sorry

end ActuarialFoundations
