-- Prove2me | Theorems.Thm_BookProof_CarlemanUnboundedHop_not_summable_inv_one_add_nat
-- name    : BookProof.CarlemanUnboundedHop.not_summable_inv_one_add_nat
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:35:44.012984+00:00
-- url     : https://prove2.me/theorems/a386c3fd-c181-4b99-aa55-2e7d18b05986
-- title:
--   `BookProof.CarlemanUnboundedHop.not_summable_inv_one_add_nat` : ¬ Summable (fun n : ℕ => (1 + (n : ℝ))⁻¹)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanUnboundedHop`.
--
--   `BookProof.CarlemanUnboundedHop.not_summable_inv_one_add_nat` : ¬ Summable (fun n : ℕ => (1 + (n : ℝ))⁻¹)
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanUnboundedHop.not_summable_inv_one_add_nat`.

-- Generated from ChapterCarlemanUnboundedHop.lean — theorem BookProof.CarlemanUnboundedHop.not_summable_inv_one_add_nat
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop



open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

theorem BookProof.CarlemanUnboundedHop.not_summable_inv_one_add_nat : ¬ Summable (fun n : ℕ => (1 + (n : ℝ))⁻¹) := by sorry
