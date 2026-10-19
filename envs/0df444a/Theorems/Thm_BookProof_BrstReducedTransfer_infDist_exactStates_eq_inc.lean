-- Prove2me | Theorems.Thm_BookProof_BrstReducedTransfer_infDist_exactStates_eq_inc
-- name    : BookProof.BrstReducedTransfer.infDist_exactStates_eq_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T18:45:10.185975+00:00
-- url     : https://prove2.me/theorems/ee802fc4-1c45-4d0e-bf0c-a426e33a6f21
-- title:
--   `BookProof.BrstReducedTransfer.infDist_exactStates_eq_inc` (hzero : ∀ x : H, U 0 x = x) (hgroup : ∀ (s t : ℝ) (x : H), U s (U t x) = U (s + t) x) (hisom : ∀ (t : ℝ) (x : H), ‖U t x‖ =
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstReducedTransfer`.
--
--   `BookProof.BrstReducedTransfer.infDist_exactStates_eq_inc` (hzero : ∀ x : H, U 0 x = x) (hgroup : ∀ (s t : ℝ) (x : H), U s (U t x) = U (s + t) x) (hisom : ∀ (t : ℝ) (x : H), ‖U t x‖ = ‖x‖) (t : ℝ) (x : H) : Metric.infDist (U t x) (exactStates Om) = Metric.infDist x (exactStates Om)
--
--   Formalization note: Lean 4 identifier `BookProof.BrstReducedTransfer.infDist_exactStates_eq_inc`.
--
--   Replaces the retired node `BookProof.BrstReducedTransfer.infDist_exactStates_eq`, whose stored statement omitted the `hcomm` hypothesis binder (dropped `include`).

-- Generated from ChapterBrstReducedTransfer.lean — theorem BookProof.BrstReducedTransfer.infDist_exactStates_eq_inc
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

include hcomm in

theorem BookProof.BrstReducedTransfer.infDist_exactStates_eq_inc (hzero : ∀ x : H, U 0 x = x)
    (hgroup : ∀ (s t : ℝ) (x : H), U s (U t x) = U (s + t) x)
    (hisom : ∀ (t : ℝ) (x : H), ‖U t x‖ = ‖x‖) (t : ℝ) (x : H) :
    Metric.infDist (U t x) (exactStates Om) = Metric.infDist x (exactStates Om) := by sorry
