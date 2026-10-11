-- Prove2me | Theorems.Thm_ActuarialFoundations_fa_increasing_term_assurance_cashflow
-- name    : ActuarialFoundations.fa_increasing_term_assurance_cashflow
-- status  : Open
-- author  : @WillR
-- created : 2026-10-11T06:55:08.069984+00:00
-- url     : https://prove2.me/theorems/ce154d7b-ca52-45e0-af12-acad7bff0e02
-- title:
--   Increasing finite-term benefits: increasing term assurance cashflow
-- statement:
--   The independently specified increasing death claims, paid at year ends, equal the corrected finite R/M commutation expression divided by D_x.
-- source:
--   Institute of Actuaries (1969–1971), International Actuarial Notation, commutation functions and increasing assurance; https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf Original-derived finite-cohort Lean statement; this exact theorem wording is not attributed to the text.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faDiscountedLives
import Definitions.Def_actuarial_faIncreasingTermAssuranceOriginal
import Definitions.Def_actuarial_faM
import Definitions.Def_actuarial_faR

namespace ActuarialFoundations

theorem fa_increasing_term_assurance_cashflow (l : ℕ → ℝ) (v : ℝ) (ω x n : ℕ) (hp : 0 < l x) (hv : 0 < v) (hxn : x+n ≤ ω) : faIncreasingTermAssuranceOriginal l v x n = (faR l v ω x - faR l v ω (x+n) - (n : ℝ) * faM l v ω (x+n)) / faDiscountedLives l v x := by sorry

end ActuarialFoundations
