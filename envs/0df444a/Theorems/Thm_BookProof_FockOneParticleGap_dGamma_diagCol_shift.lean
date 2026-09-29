-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_dGamma_diagCol_shift
-- name    : BookProof.FockOneParticleGap.dGamma_diagCol_shift
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:35:46.838747+00:00
-- url     : https://prove2.me/theorems/3dcd5d58-bf73-46c4-8bbe-47b464d88c5a
-- title:
--   (e : ℕ → ℝ) (mu : ℝ) (u : FockAlg) : dGamma (diagCol fun k => e k + mu) u = dGamma (diagCol e) u + ((mu : ℝ) : ℂ) • dGamma numberCol u
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.dGamma_diagCol_shift` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.dGamma_diagCol_shift
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap












noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

theorem BookProof.FockOneParticleGap.dGamma_diagCol_shift (e : ℕ → ℝ) (mu : ℝ) (u : FockAlg) :
    dGamma (diagCol fun k => e k + mu) u
      = dGamma (diagCol e) u + ((mu : ℝ) : ℂ) • dGamma numberCol u := by sorry
