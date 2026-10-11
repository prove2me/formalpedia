-- Prove2me | Theorems.Thm_BookProof_WeakSecondDeriv_integrable_test_smul
-- name    : BookProof.WeakSecondDeriv.integrable_test_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:10:41.561949+00:00
-- url     : https://prove2.me/theorems/a6195468-31cd-4850-8fcf-865582f1c12f
-- title:
--   `BookProof.WeakSecondDeriv.integrable_test_smul` {φ : ℝ → ℝ} (hφ : IsTestFun φ) {r : ℝ → F} (hr : LocallyIntegrable r volume) : Integrable (fun x => φ x • r x) volume
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakSecondDerivative`.
--
--   `BookProof.WeakSecondDeriv.integrable_test_smul` {φ : ℝ → ℝ} (hφ : IsTestFun φ) {r : ℝ → F} (hr : LocallyIntegrable r volume) : Integrable (fun x => φ x • r x) volume
--
--   Formalization note: Lean 4 identifier `BookProof.WeakSecondDeriv.integrable_test_smul`.

-- Generated from ChapterWeakSecondDerivative.lean — theorem BookProof.WeakSecondDeriv.integrable_test_smul
import Mathlib
import Definitions.Def_ChapterWeakSecondDerivative
open BookProof.WeakSecondDeriv



open MeasureTheory Filter Topology intervalIntegral Set

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem BookProof.WeakSecondDeriv.integrable_test_smul {φ : ℝ → ℝ} (hφ : IsTestFun φ) {r : ℝ → F}
    (hr : LocallyIntegrable r volume) : Integrable (fun x => φ x • r x) volume := by sorry
