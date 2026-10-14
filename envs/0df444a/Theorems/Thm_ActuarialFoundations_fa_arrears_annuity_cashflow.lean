-- Prove2me | Theorems.Thm_ActuarialFoundations_fa_arrears_annuity_cashflow
-- name    : ActuarialFoundations.fa_arrears_annuity_cashflow
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-11T06:53:03.455001+00:00
-- url     : https://prove2.me/theorems/7bc69a23-153a-475c-8d6d-b74ae59120c6
-- title:
--   Deferred and arrears annuities and assurances: arrears annuity cashflow
-- statement:
--   The annuity in arrears excludes the immediate instalment and includes the terminal-survival payment at maturity, which vanishes under l_ω=0. Therefore its value is (N_x−D_x)/D_x.
-- source:
--   S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., Chapters 4 and 7; Wiley https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782521 Original-derived finite-cohort Lean statement; this exact theorem wording is not attributed to the text.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faAnnuityArrearsOriginal
import Definitions.Def_actuarial_faDiscountedLives
import Definitions.Def_actuarial_faN

namespace ActuarialFoundations

theorem fa_arrears_annuity_cashflow (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) (hp : 0 < l x) (hv : 0 < v) (hx : x ≤ ω) (hω : l ω = 0) : faAnnuityArrearsOriginal l v ω x = (faN l v ω x - faDiscountedLives l v x) / faDiscountedLives l v x := by sorry

end ActuarialFoundations
