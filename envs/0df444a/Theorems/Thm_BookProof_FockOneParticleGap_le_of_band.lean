-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_le_of_band
-- name    : BookProof.FockOneParticleGap.le_of_band
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:12:41.969327+00:00
-- url     : https://prove2.me/theorems/aa034d45-4957-4b3a-8353-fee84760fe4a
-- title:
--   {lo hi : ℕ → ℝ} {lam mu : ℝ} (hmem : ∀ m, lam ∈ Set.Icc (lo m) (hi m)) {m : ℕ} (hlo : mu ≤ lo m) : mu ≤ lam
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.le_of_band` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.le_of_band
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap












noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

theorem BookProof.FockOneParticleGap.le_of_band {lo hi : ℕ → ℝ} {lam mu : ℝ} (hmem : ∀ m, lam ∈ Set.Icc (lo m) (hi m))
    {m : ℕ} (hlo : mu ≤ lo m) : mu ≤ lam := by sorry
