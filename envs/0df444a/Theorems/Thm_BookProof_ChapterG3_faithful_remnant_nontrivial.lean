-- Prove2me | Theorems.Thm_BookProof_ChapterG3_faithful_remnant_nontrivial
-- name    : BookProof.ChapterG3.faithful_remnant_nontrivial
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T11:35:37.129419+00:00
-- url     : https://prove2.me/theorems/d04ec55e-6386-41a2-a415-b75374475064
-- title:
--   `BookProof.ChapterG3.faithful_remnant_nontrivial` {G Y : Type*} [Group G] [MulAction G Y] [FaithfulSMul G Y] [Nontrivial G] : ∃ (g : G) (y : Y), g • y ≠ y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG3`.
--
--   `BookProof.ChapterG3.faithful_remnant_nontrivial` {G Y : Type*} [Group G] [MulAction G Y] [FaithfulSMul G Y] [Nontrivial G] : ∃ (g : G) (y : Y), g • y ≠ y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG3.faithful_remnant_nontrivial`.

-- Generated from ChapterG3.lean — theorem BookProof.ChapterG3.faithful_remnant_nontrivial
import Mathlib
import Definitions.Def_ChapterG3
open BookProof.ChapterG3


open MeasureTheory
open scoped ENNReal



variable {X : Type*}

theorem BookProof.ChapterG3.faithful_remnant_nontrivial {G Y : Type*} [Group G] [MulAction G Y]
    [FaithfulSMul G Y] [Nontrivial G] : ∃ (g : G) (y : Y), g • y ≠ y := by sorry
