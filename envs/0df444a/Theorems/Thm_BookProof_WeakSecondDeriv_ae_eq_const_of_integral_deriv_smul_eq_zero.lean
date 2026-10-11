-- Prove2me | Theorems.Thm_BookProof_WeakSecondDeriv_ae_eq_const_of_integral_deriv_smul_eq_zero
-- name    : BookProof.WeakSecondDeriv.ae_eq_const_of_integral_deriv_smul_eq_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:10:50.132106+00:00
-- url     : https://prove2.me/theorems/93684ba8-dc22-4085-9537-ae3e04a16086
-- title:
--   `BookProof.WeakSecondDeriv.ae_eq_const_of_integral_deriv_smul_eq_zero` {r : ℝ → F} (hr : LocallyIntegrable r volume) (h : ∀ g : ℝ → ℝ, IsTestFun g → ∫ x, deriv g x • r x = 0) : ∃ c
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakSecondDerivative`.
--
--   `BookProof.WeakSecondDeriv.ae_eq_const_of_integral_deriv_smul_eq_zero` {r : ℝ → F} (hr : LocallyIntegrable r volume) (h : ∀ g : ℝ → ℝ, IsTestFun g → ∫ x, deriv g x • r x = 0) : ∃ c : F, r =ᵐ[volume] fun _ => c
--
--   Formalization note: Lean 4 identifier `BookProof.WeakSecondDeriv.ae_eq_const_of_integral_deriv_smul_eq_zero`.

-- Generated from ChapterWeakSecondDerivative.lean — theorem BookProof.WeakSecondDeriv.ae_eq_const_of_integral_deriv_smul_eq_zero
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval
open BookProof.WeakSecondDeriv



open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem BookProof.WeakSecondDeriv.ae_eq_const_of_integral_deriv_smul_eq_zero {r : ℝ → F}
    (hr : LocallyIntegrable r volume)
    (h : ∀ g : ℝ → ℝ, IsTestFun g → ∫ x, deriv g x • r x = 0) :
    ∃ c : F, r =ᵐ[volume] fun _ => c := by sorry
