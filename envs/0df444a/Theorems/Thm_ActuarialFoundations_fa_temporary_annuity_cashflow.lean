-- Prove2me | Theorems.Thm_ActuarialFoundations_fa_temporary_annuity_cashflow
-- name    : ActuarialFoundations.fa_temporary_annuity_cashflow
-- status  : Open
-- author  : @WillR
-- created : 2026-10-11T06:49:36.703854+00:00
-- url     : https://prove2.me/theorems/ba29d9e0-3ca7-4edb-b07b-aed74facc849
-- title:
--   Pure endowments and finite-term annuities: temporary annuity cashflow
-- statement:
--   A temporary annuity-due is calculated from the original n payments and separately shown equal to (N_x−N_(x+n))/D_x. There is no payment at duration n.
-- source:
--   David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, 3rd ed., Chapters 4–5; Cambridge University Press https://doi.org/10.1017/9781108784184 Original-derived finite-cohort Lean statement; this exact theorem wording is not attributed to the text.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faDiscountedLives
import Definitions.Def_actuarial_faN
import Definitions.Def_actuarial_faTemporaryAnnuityOriginal

namespace ActuarialFoundations

theorem fa_temporary_annuity_cashflow (l : ℕ → ℝ) (v : ℝ) (ω x n : ℕ) (hp : 0 < l x) (hv : 0 < v) (hxn : x+n ≤ ω) : faTemporaryAnnuityOriginal l v x n = (faN l v ω x - faN l v ω (x+n)) / faDiscountedLives l v x := by sorry

end ActuarialFoundations
