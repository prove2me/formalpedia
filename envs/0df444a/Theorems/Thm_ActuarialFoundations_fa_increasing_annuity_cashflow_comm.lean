-- Prove2me | Theorems.Thm_ActuarialFoundations_fa_increasing_annuity_cashflow_comm
-- name    : ActuarialFoundations.fa_increasing_annuity_cashflow_comm
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T23:35:10.309013+00:00
-- url     : https://prove2.me/theorems/9a1d3d15-3f8e-4c72-933b-a056e70494e1
-- title:
--   Increasing annuity cashflow comm
-- statement:
--   Prove equality of independently defined original cashflows and the corresponding commutation expression for the stated exact Lean assumptions, directly from the life-table and cashflow definitions. Survivor benefits are valued on beginning-year anniversaries, with zero-lives boundary treatment. No commutation equivalence or desired result may be inserted as a hypothesis.
-- source:
--   Institute of Actuaries (1971), International Actuarial Notation, commutation functions, p.50, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf. Original derived theorem; not a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faDiscountedLives
import Definitions.Def_actuarial_faS
import Definitions.Def_actuarial_faIncreasingAnnuityOriginal

namespace ActuarialFoundations

theorem fa_increasing_annuity_cashflow_comm (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) (hx : l x ≠ 0) (hv : v ≠ 0) : faIncreasingAnnuityOriginal l v ω x = faS l v ω x / faDiscountedLives l v x := by sorry

end ActuarialFoundations
