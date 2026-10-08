-- Prove2me | Theorems.Thm_BookProof_BrstReducedTransfer_infDist_exactStates_eq
-- name    : BookProof.BrstReducedTransfer.infDist_exactStates_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:11:16.511093+00:00
-- url     : https://prove2.me/theorems/7c8f0b9b-0d20-41b7-af1d-ef65ebb53580
-- title:
--   `BookProof.BrstReducedTransfer.infDist_exactStates_eq` (hzero : ∀ x : H, U 0 x = x) (hgroup : ∀ (s t : ℝ) (x : H), U s (U t x) = U (s + t) x) (hisom : ∀ (t : ℝ) (x : H), ‖U t x‖ =
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstReducedTransfer`.
--
--   `BookProof.BrstReducedTransfer.infDist_exactStates_eq` (hzero : ∀ x : H, U 0 x = x) (hgroup : ∀ (s t : ℝ) (x : H), U s (U t x) = U (s + t) x) (hisom : ∀ (t : ℝ) (x : H), ‖U t x‖ = ‖x‖) (t : ℝ) (x : H) : Metric.infDist (U t x) (exactStates Om) = Metric.infDist x (exactStates Om)
--
--   Formalization note: Lean 4 identifier `BookProof.BrstReducedTransfer.infDist_exactStates_eq`.

-- Generated from ChapterBrstReducedTransfer.lean — theorem BookProof.BrstReducedTransfer.infDist_exactStates_eq
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstReducedTransfer
open BookProof.BrstReducedTransfer



open BookProof BookProof.ChapterStoneResolvent


variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

variable (Om : H →L[ℂ] H)

variable {Om}
variable (Om)
variable (U : ℝ → (H →L[ℂ] H)) (hcomm : ∀ (t : ℝ) (y : H), U t (Om y) = Om (U t y))

theorem BookProof.BrstReducedTransfer.infDist_exactStates_eq (hzero : ∀ x : H, U 0 x = x)
    (hgroup : ∀ (s t : ℝ) (x : H), U s (U t x) = U (s + t) x)
    (hisom : ∀ (t : ℝ) (x : H), ‖U t x‖ = ‖x‖) (t : ℝ) (x : H) :
    Metric.infDist (U t x) (exactStates Om) = Metric.infDist x (exactStates Om) := by sorry
