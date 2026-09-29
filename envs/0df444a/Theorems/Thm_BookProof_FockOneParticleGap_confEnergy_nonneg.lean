-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_confEnergy_nonneg
-- name    : BookProof.FockOneParticleGap.confEnergy_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:04:55.096701+00:00
-- url     : https://prove2.me/theorems/a0df96e7-dffc-4b35-aaa8-f46e00822b09
-- title:
--   {e : ℕ → ℝ} (he : ∀ k, 0 ≤ e k) (β : Conf) : 0 ≤ confEnergy e β
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.confEnergy_nonneg` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.confEnergy_nonneg
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap












noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

theorem BookProof.FockOneParticleGap.confEnergy_nonneg {e : ℕ → ℝ} (he : ∀ k, 0 ≤ e k) (β : Conf) :
    0 ≤ confEnergy e β := by sorry
