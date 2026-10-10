-- Prove2me | Theorems.Thm_BookProof_ChapterG_swap_mem_gaugeGroup
-- name    : BookProof.ChapterG.swap_mem_gaugeGroup
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:45:23.554023+00:00
-- url     : https://prove2.me/theorems/fc2d77e0-34ee-44ee-a57f-7b9170772a03
-- title:
--   `BookProof.ChapterG.swap_mem_gaugeGroup` {X Y : Type*} [DecidableEq X] {π : X → Y} {x x' : X} (h : π x = π x') : Equiv.swap x x' ∈ gaugeGroup π
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG`.
--
--   `BookProof.ChapterG.swap_mem_gaugeGroup` {X Y : Type*} [DecidableEq X] {π : X → Y} {x x' : X} (h : π x = π x') : Equiv.swap x x' ∈ gaugeGroup π
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG.swap_mem_gaugeGroup`.

-- Generated from ChapterG.lean — theorem BookProof.ChapterG.swap_mem_gaugeGroup
import Mathlib
import Definitions.Def_ChapterG
open BookProof.ChapterG


open scoped ComplexConjugate InnerProductSpace Matrix

theorem BookProof.ChapterG.swap_mem_gaugeGroup {X Y : Type*} [DecidableEq X] {π : X → Y}
    {x x' : X} (h : π x = π x') :
    Equiv.swap x x' ∈ gaugeGroup π := by sorry
