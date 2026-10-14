-- Prove2me | Theorems.Thm_ActuarialFoundations_fa_annuity_cashflow_comm
-- name    : ActuarialFoundations.fa_annuity_cashflow_comm
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T23:33:03.947973+00:00
-- url     : https://prove2.me/theorems/2044ee58-07e7-43ee-88f7-c409d827db9f
-- title:
--   Annuity cashflow comm
-- statement:
--   Prove equality of independently defined original cashflows and the corresponding commutation expression for the stated exact Lean assumptions, directly from the life-table and cashflow definitions. Survivor benefits are valued on beginning-year anniversaries, with zero-lives boundary treatment. No commutation equivalence or desired result may be inserted as a hypothesis.
-- source:
--   Institute of Actuaries (1971), International Actuarial Notation, commutation functions, p.50, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf. Original derived theorem; not a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faDiscountedLives
import Definitions.Def_actuarial_faN
import Definitions.Def_actuarial_faAnnuityOriginal

namespace ActuarialFoundations

theorem fa_annuity_cashflow_comm (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) (hx : l x ≠ 0) (hv : v ≠ 0) : faAnnuityOriginal l v ω x = faN l v ω x / faDiscountedLives l v x := by sorry

end ActuarialFoundations
