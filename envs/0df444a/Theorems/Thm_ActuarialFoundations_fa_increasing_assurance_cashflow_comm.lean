-- Prove2me | Theorems.Thm_ActuarialFoundations_fa_increasing_assurance_cashflow_comm
-- name    : ActuarialFoundations.fa_increasing_assurance_cashflow_comm
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T23:35:36.200981+00:00
-- url     : https://prove2.me/theorems/82595b89-0e2e-4acf-97df-d71cebc99e87
-- title:
--   Increasing assurance cashflow comm
-- statement:
--   Prove equality of independently defined original cashflows and the corresponding commutation expression for the stated exact Lean assumptions, directly from the life-table and cashflow definitions. The claim is valued at the end of the death year, and terminal-age endpoints are disjoint. No commutation equivalence or desired result may be inserted as a hypothesis.
-- source:
--   Institute of Actuaries (1971), International Actuarial Notation, commutation functions, p.50, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf. Original derived theorem; not a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faDiscountedLives
import Definitions.Def_actuarial_faR
import Definitions.Def_actuarial_faIncreasingAssuranceOriginal

namespace ActuarialFoundations

theorem fa_increasing_assurance_cashflow_comm (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) (hx : l x ≠ 0) (hv : v ≠ 0) : faIncreasingAssuranceOriginal l v ω x = faR l v ω x / faDiscountedLives l v x := by sorry

end ActuarialFoundations
