-- Prove2me | Theorems.Thm_BookProof_BandEnclosure_nestedBands_le
-- name    : BookProof.BandEnclosure.nestedBands_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:58:39.754013+00:00
-- url     : https://prove2.me/theorems/6eb21e5f-2eb4-4c6a-a149-87c1500c9415
-- title:
--   {lo hi : ℕ → ℝ} (h : NestedBands lo hi) {m n : ℕ} (hmn : m ≤ n) : Set.Icc (lo n) (hi n) ⊆ Set.Icc (lo m) (hi m)
-- statement:
--   Lean 4 theorem `BookProof.BandEnclosure.nestedBands_le` (module `BookProof.BandEnclosure`), source chapter `BookProof/ChapterBandEnclosure.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterBandEnclosure.lean

-- Generated from ChapterBandEnclosure.lean — theorem BookProof.BandEnclosure.nestedBands_le
import Mathlib
import Definitions.Def_ChapterBandEnclosure
open BookProof.BandEnclosure










noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterH6 BookProof.ChapterH8

theorem BookProof.BandEnclosure.nestedBands_le {lo hi : ℕ → ℝ} (h : NestedBands lo hi) {m n : ℕ} (hmn : m ≤ n) :
    Set.Icc (lo n) (hi n) ⊆ Set.Icc (lo m) (hi m) := by sorry
