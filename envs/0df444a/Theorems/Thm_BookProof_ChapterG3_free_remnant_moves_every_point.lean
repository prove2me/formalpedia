-- Prove2me | Theorems.Thm_BookProof_ChapterG3_free_remnant_moves_every_point
-- name    : BookProof.ChapterG3.free_remnant_moves_every_point
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T11:35:44.306288+00:00
-- url     : https://prove2.me/theorems/42c4a851-4f99-49e1-9544-5b27b3b2793b
-- title:
--   `BookProof.ChapterG3.free_remnant_moves_every_point` {G Y : Type*} [Group G] [MulAction G Y] (hfree : ∀ (g : G) (y : Y), g • y = y → g = 1) {g : G} (hg : g ≠ 1) (y : Y) : g • y ≠ y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG3`.
--
--   `BookProof.ChapterG3.free_remnant_moves_every_point` {G Y : Type*} [Group G] [MulAction G Y] (hfree : ∀ (g : G) (y : Y), g • y = y → g = 1) {g : G} (hg : g ≠ 1) (y : Y) : g • y ≠ y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG3.free_remnant_moves_every_point`.

-- Generated from ChapterG3.lean — theorem BookProof.ChapterG3.free_remnant_moves_every_point
import Mathlib
import Definitions.Def_ChapterG3
open BookProof.ChapterG3


open MeasureTheory
open scoped ENNReal



variable {X : Type*}

theorem BookProof.ChapterG3.free_remnant_moves_every_point {G Y : Type*} [Group G] [MulAction G Y]
    (hfree : ∀ (g : G) (y : Y), g • y = y → g = 1) {g : G} (hg : g ≠ 1) (y : Y) :
    g • y ≠ y := by sorry
