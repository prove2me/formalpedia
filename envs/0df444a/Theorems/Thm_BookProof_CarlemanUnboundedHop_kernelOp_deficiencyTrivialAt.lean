-- Prove2me | Theorems.Thm_BookProof_CarlemanUnboundedHop_kernelOp_deficiencyTrivialAt
-- name    : BookProof.CarlemanUnboundedHop.kernelOp_deficiencyTrivialAt
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T10:29:35.412982+00:00
-- url     : https://prove2.me/theorems/301011a0-5554-4eae-8f6e-7dd0af76252c
-- title:
--   `BookProof.CarlemanUnboundedHop.kernelOp_deficiencyTrivialAt` {a : ℕ → ℕ → ℂ} {A θ Θ : ℕ → ℝ} (hk : IsL2Kernel a) (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanUnboundedHop`.
--
--   `BookProof.CarlemanUnboundedHop.kernelOp_deficiencyTrivialAt` {a : ℕ → ℕ → ℂ} {A θ Θ : ℕ → ℝ} (hk : IsL2Kernel a) (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (hΘsum : Summable Θ) (hApos : ∀ n, 0 < A n) (hAmono : Monotone A) (hbd : ∀ n k, n < k → ‖a n k‖ ≤ A n * θ (k - n)) (hcar : ¬ Summable fun n => (A n)⁻¹) {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt (lpFiniteModes ℕ) (kernelOp hk) z
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanUnboundedHop.kernelOp_deficiencyTrivialAt`.

-- Generated from ChapterCarlemanUnboundedHop.lean — theorem BookProof.CarlemanUnboundedHop.kernelOp_deficiencyTrivialAt
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterKernelBound
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.KernelBound
open BookProof.CarlemanUnboundedHop



open Finset
open BookProof.FarisLavine
open BookProof.NavierStokesFlow

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

theorem BookProof.CarlemanUnboundedHop.kernelOp_deficiencyTrivialAt {a : ℕ → ℕ → ℂ} {A θ Θ : ℕ → ℝ} (hk : IsL2Kernel a)
    (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j))
    (hΘsum : Summable Θ) (hApos : ∀ n, 0 < A n) (hAmono : Monotone A)
    (hbd : ∀ n k, n < k → ‖a n k‖ ≤ A n * θ (k - n))
    (hcar : ¬ Summable fun n => (A n)⁻¹) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (lpFiniteModes ℕ) (kernelOp hk) z := by sorry
