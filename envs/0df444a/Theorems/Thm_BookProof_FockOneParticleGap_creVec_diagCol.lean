-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_creVec_diagCol
-- name    : BookProof.FockOneParticleGap.creVec_diagCol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:09:51.465131+00:00
-- url     : https://prove2.me/theorems/28030854-759e-4e6e-9b28-ef5a2073b707
-- title:
--   (e : ℕ → ℝ) (k : ℕ) (x : FockAlg) : creVec (diagCol e k) x = ((e k : ℝ) : ℂ) • creA k x
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.creVec_diagCol` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.creVec_diagCol
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap












noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

theorem BookProof.FockOneParticleGap.creVec_diagCol (e : ℕ → ℝ) (k : ℕ) (x : FockAlg) :
    creVec (diagCol e k) x = ((e k : ℝ) : ℂ) • creA k x := by sorry
