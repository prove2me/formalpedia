-- Prove2me | Theorems.Thm_ActuarialFoundations_fa_comprehensive_finite_valuation
-- name    : ActuarialFoundations.fa_comprehensive_finite_valuation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-11T06:56:04.218962+00:00
-- url     : https://prove2.me/theorems/3d1540d9-7194-490d-a0e2-de68c8167f04
-- title:
--   Finite-horizon conservation and comprehensive valuation: comprehensive finite valuation
-- statement:
--   The comprehensive finite-cohort valuation theorem combines the original 15-conclusion whole-life foundation with the new finite-term family. Its hypotheses do not assume an annuity or assurance relationship, and its proof must derive both prerequisite capstones.
-- source:
--   Institute of Actuaries (1969–1971), International Actuarial Notation, commutation and assurance-annuity relations; https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf Original-derived finite-cohort Lean statement; this exact theorem wording is not attributed to the text.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faAnnuityArrearsOriginal
import Definitions.Def_actuarial_faAnnuityOriginal
import Definitions.Def_actuarial_faAssuranceOriginal
import Definitions.Def_actuarial_faDeaths
import Definitions.Def_actuarial_faDeferredAnnuityOriginal
import Definitions.Def_actuarial_faDeferredAssuranceOriginal
import Definitions.Def_actuarial_faDeferredMortality
import Definitions.Def_actuarial_faDiscountedDeaths
import Definitions.Def_actuarial_faDiscountedLives
import Definitions.Def_actuarial_faEndowmentAssuranceOriginal
import Definitions.Def_actuarial_faFiniteCohortValid
import Definitions.Def_actuarial_faIncreasingAnnuityOriginal
import Definitions.Def_actuarial_faIncreasingAssuranceOriginal
import Definitions.Def_actuarial_faIncreasingTemporaryAnnuityOriginal
import Definitions.Def_actuarial_faIncreasingTermAssuranceOriginal
import Definitions.Def_actuarial_faM
import Definitions.Def_actuarial_faMultiYearMortality
import Definitions.Def_actuarial_faN
import Definitions.Def_actuarial_faOneYearMortality
import Definitions.Def_actuarial_faPureEndowmentOriginal
import Definitions.Def_actuarial_faR
import Definitions.Def_actuarial_faRAbsolute
import Definitions.Def_actuarial_faS
import Definitions.Def_actuarial_faSurvival
import Definitions.Def_actuarial_faTemporaryAnnuityOriginal
import Definitions.Def_actuarial_faTermAssuranceOriginal

namespace ActuarialFoundations

theorem fa_comprehensive_finite_valuation (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) (h : faFiniteCohortValid l ω) (hx : x < ω) (hp : 0 < l x) (hv : 0 < v) (hv1 : v ≤ 1) : ((faSurvival l x 0 = 1) ∧ (faSurvival l x (ω-x) = 0) ∧ (∀ n, x+n ≤ ω → 0 ≤ faSurvival l x n ∧ faSurvival l x n ≤ 1) ∧ ((∑ k ∈ Finset.range (ω-x), faDeaths l (x+k) / l x) = 1) ∧ ((∑ k ∈ Finset.range (ω-x), faDeaths l (x+k)) = l x) ∧ (faAnnuityOriginal l v ω x = faN l v ω x / faDiscountedLives l v x) ∧ (faAssuranceOriginal l v ω x = faM l v ω x / faDiscountedLives l v x) ∧ (faN l v ω x = faDiscountedLives l v x + faN l v ω (x+1)) ∧ (faM l v ω x = faDiscountedDeaths l v x + faM l v ω (x+1)) ∧ (faS l v ω x = faN l v ω x + faS l v ω (x+1)) ∧ (faR l v ω x = faM l v ω x + faR l v ω (x+1)) ∧ (faIncreasingAnnuityOriginal l v ω x = faS l v ω x / faDiscountedLives l v x) ∧ (faIncreasingAssuranceOriginal l v ω x = faR l v ω x / faDiscountedLives l v x) ∧ (faRAbsolute l v ω x = faR l v ω x + (x : ℝ) * faM l v ω x) ∧ (faAssuranceOriginal l v ω x + (1-v)*faAnnuityOriginal l v ω x = 1)) ∧ ((faOneYearMortality l x + faSurvival l x 1 = 1) ∧ (faAnnuityArrearsOriginal l v ω x = (faN l v ω x - faDiscountedLives l v x) / faDiscountedLives l v x) ∧ (faM l v ω x + (1-v) * faN l v ω x = faDiscountedLives l v x) ∧ (∀ n : ℕ, x+n ≤ ω → (faMultiYearMortality l x n + faSurvival l x n = 1) ∧ (faPureEndowmentOriginal l v x n = faDiscountedLives l v (x+n) / faDiscountedLives l v x) ∧ (faTemporaryAnnuityOriginal l v x n = (faN l v ω x - faN l v ω (x+n)) / faDiscountedLives l v x) ∧ (faTermAssuranceOriginal l v x n = (faM l v ω x - faM l v ω (x+n)) / faDiscountedLives l v x) ∧ (faEndowmentAssuranceOriginal l v x n = (faM l v ω x - faM l v ω (x+n) + faDiscountedLives l v (x+n)) / faDiscountedLives l v x) ∧ (faIncreasingTemporaryAnnuityOriginal l v x n = (faS l v ω x - faS l v ω (x+n) - (n : ℝ) * faN l v ω (x+n)) / faDiscountedLives l v x) ∧ (faIncreasingTermAssuranceOriginal l v x n = (faR l v ω x - faR l v ω (x+n) - (n : ℝ) * faM l v ω (x+n)) / faDiscountedLives l v x) ∧ ((faM l v ω x - faM l v ω (x+n)) + (1-v) * (faN l v ω x - faN l v ω (x+n)) + faDiscountedLives l v (x+n) = faDiscountedLives l v x) ∧ (faDeferredAnnuityOriginal l v ω x n = faN l v ω (x+n) / faDiscountedLives l v x) ∧ (faDeferredAssuranceOriginal l v ω x n = faM l v ω (x+n) / faDiscountedLives l v x) ∧ (∀ t : ℕ, x+n+t ≤ ω → 0 ≤ faSurvival l x (n+t) ∧ faSurvival l x (n+t) ≤ faSurvival l x n ∧ faSurvival l x n ≤ 1) ∧ (∀ t : ℕ, x+n+t ≤ ω → 0 < l (x+n) → faSurvival l x (n+t) = faSurvival l x n * faSurvival l (x+n) t ∧ faDeferredMortality l x n t = faSurvival l x n * faMultiYearMortality l (x+n) t) ∧ (∀ t r : ℕ, x+n+t+r ≤ ω → faDeferredMortality l x n t + faDeferredMortality l x (n+t) r = faDeferredMortality l x n (t+r)))) := by sorry

end ActuarialFoundations
