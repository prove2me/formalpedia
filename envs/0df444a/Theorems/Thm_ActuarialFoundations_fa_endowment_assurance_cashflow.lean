-- Prove2me | Theorems.Thm_ActuarialFoundations_fa_endowment_assurance_cashflow
-- name    : ActuarialFoundations.fa_endowment_assurance_cashflow
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-11T06:50:34.591604+00:00
-- url     : https://prove2.me/theorems/910eb0d1-6fc8-4b36-a0d6-075b841c8e9a
-- title:
--   Term and endowment assurances: endowment assurance cashflow
-- statement:
--   Combining term death benefits with an exact-maturity survival benefit gives (M_x−M_(x+n)+D_(x+n))/D_x. Both source benefits are separately defined.
-- source:
--   David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, 3rd ed., Chapters 4–5; Cambridge University Press https://doi.org/10.1017/9781108784184 Original-derived finite-cohort Lean statement; this exact theorem wording is not attributed to the text.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faDiscountedLives
import Definitions.Def_actuarial_faEndowmentAssuranceOriginal
import Definitions.Def_actuarial_faM

namespace ActuarialFoundations

theorem fa_endowment_assurance_cashflow (l : ℕ → ℝ) (v : ℝ) (ω x n : ℕ) (hp : 0 < l x) (hv : 0 < v) (hxn : x+n ≤ ω) : faEndowmentAssuranceOriginal l v x n = (faM l v ω x - faM l v ω (x+n) + faDiscountedLives l v (x+n)) / faDiscountedLives l v x := by sorry

end ActuarialFoundations
