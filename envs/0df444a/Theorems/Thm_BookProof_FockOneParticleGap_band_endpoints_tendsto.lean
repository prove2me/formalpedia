-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_band_endpoints_tendsto
-- name    : BookProof.FockOneParticleGap.band_endpoints_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:03:28.376235+00:00
-- url     : https://prove2.me/theorems/22f727ed-9c8e-4462-905f-ae58f979642d
-- title:
--   {lo hi : ℕ → ℝ} {lam : ℝ} (hmem : ∀ m, lam ∈ Set.Icc (lo m) (hi m)) (hwidth : Tendsto (fun m => hi m - lo m) atTop (𝓝 0)) : Tendsto lo atTop (𝓝 lam) ∧ Tendsto hi atTop (𝓝 lam)
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.band_endpoints_tendsto` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.band_endpoints_tendsto
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap












noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

theorem BookProof.FockOneParticleGap.band_endpoints_tendsto {lo hi : ℕ → ℝ} {lam : ℝ}
    (hmem : ∀ m, lam ∈ Set.Icc (lo m) (hi m))
    (hwidth : Tendsto (fun m => hi m - lo m) atTop (𝓝 0)) :
    Tendsto lo atTop (𝓝 lam) ∧ Tendsto hi atTop (𝓝 lam) := by sorry
