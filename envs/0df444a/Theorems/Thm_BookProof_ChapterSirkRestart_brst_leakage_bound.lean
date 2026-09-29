-- Prove2me | Theorems.Thm_BookProof_ChapterSirkRestart_brst_leakage_bound
-- name    : BookProof.ChapterSirkRestart.brst_leakage_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T08:03:03.069751+00:00
-- url     : https://prove2.me/theorems/42a98512-c147-4e94-ba8b-92422ccbec02
-- title:
--   (U S Om : E →L[ℂ] E) (eps : ℝ) (hU : ∀ w : E, ‖U w‖ ≤ ‖w‖) (hS : ∀ w : E, ‖S w‖ ≤ ‖w‖) (hstep : ∀ w : E, ‖U w - S w‖ ≤ eps * ‖w‖) (hcomm : Om.comp U =...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkRestart.brst_leakage_bound` (module `BookProof.ChapterSirkRestart`), source chapter `BookProof/ChapterChapterSirkRestart.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkRestart.lean

-- Generated from ChapterSirkRestart.lean — theorem BookProof.ChapterSirkRestart.brst_leakage_bound
import Mathlib
import Definitions.Def_ChapterSirkRestart
open BookProof.ChapterSirkRestart







noncomputable section

open Filter Topology


open BookProof.ChapterH6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterSirkRestart.brst_leakage_bound (U S Om : E →L[ℂ] E) (eps : ℝ)
    (hU : ∀ w : E, ‖U w‖ ≤ ‖w‖) (hS : ∀ w : E, ‖S w‖ ≤ ‖w‖)
    (hstep : ∀ w : E, ‖U w - S w‖ ≤ eps * ‖w‖)
    (hcomm : Om.comp U = U.comp Om)
    (n : ℕ) (v : E) (hv : Om v = 0) :
    ‖Om ((S ^ n) v)‖ ≤ ‖Om‖ * (n * eps * ‖v‖) := by sorry
