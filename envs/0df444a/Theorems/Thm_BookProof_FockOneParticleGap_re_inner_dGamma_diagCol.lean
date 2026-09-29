-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_re_inner_dGamma_diagCol
-- name    : BookProof.FockOneParticleGap.re_inner_dGamma_diagCol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:36:29.788496+00:00
-- url     : https://prove2.me/theorems/fd257706-955d-4ea5-bc69-0f15dd2c3aba
-- title:
--   (e : ℕ → ℝ) (u : FockAlg) : (inner ℂ (toLp u) (toLp (dGamma (diagCol e) u)) : ℂ).re = ∑ α ∈ u.support, confEnergy e α * ‖u α‖ ^ 2
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.re_inner_dGamma_diagCol` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.re_inner_dGamma_diagCol
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap












noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

theorem BookProof.FockOneParticleGap.re_inner_dGamma_diagCol (e : ℕ → ℝ) (u : FockAlg) :
    (inner ℂ (toLp u) (toLp (dGamma (diagCol e) u)) : ℂ).re
      = ∑ α ∈ u.support, confEnergy e α * ‖u α‖ ^ 2 := by sorry
