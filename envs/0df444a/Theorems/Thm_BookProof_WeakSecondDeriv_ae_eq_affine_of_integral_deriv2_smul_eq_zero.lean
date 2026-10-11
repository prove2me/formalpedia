-- Prove2me | Theorems.Thm_BookProof_WeakSecondDeriv_ae_eq_affine_of_integral_deriv2_smul_eq_zero
-- name    : BookProof.WeakSecondDeriv.ae_eq_affine_of_integral_deriv2_smul_eq_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:10:53.322505+00:00
-- url     : https://prove2.me/theorems/9726b6bf-c510-4411-accd-d9285c0bcb01
-- title:
--   `BookProof.WeakSecondDeriv.ae_eq_affine_of_integral_deriv2_smul_eq_zero` {r : ℝ → F} (hr : LocallyIntegrable r volume) (h : ∀ g : ℝ → ℝ, IsTestFun g → ∫ x, deriv (deriv g) x • r x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakSecondDerivative`.
--
--   `BookProof.WeakSecondDeriv.ae_eq_affine_of_integral_deriv2_smul_eq_zero` {r : ℝ → F} (hr : LocallyIntegrable r volume) (h : ∀ g : ℝ → ℝ, IsTestFun g → ∫ x, deriv (deriv g) x • r x = 0) : ∃ a b : F, r =ᵐ[volume] fun x => x • a + b
--
--   Formalization note: Lean 4 identifier `BookProof.WeakSecondDeriv.ae_eq_affine_of_integral_deriv2_smul_eq_zero`.

-- Generated from ChapterWeakSecondDerivative.lean — theorem BookProof.WeakSecondDeriv.ae_eq_affine_of_integral_deriv2_smul_eq_zero
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval
open BookProof.WeakSecondDeriv



open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem BookProof.WeakSecondDeriv.ae_eq_affine_of_integral_deriv2_smul_eq_zero {r : ℝ → F}
    (hr : LocallyIntegrable r volume)
    (h : ∀ g : ℝ → ℝ, IsTestFun g → ∫ x, deriv (deriv g) x • r x = 0) :
    ∃ a b : F, r =ᵐ[volume] fun x => x • a + b := by sorry
