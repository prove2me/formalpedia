-- Prove2me | Theorems.Thm_BookProof_FockNumberPreservingGap_dGamma_shiftCol
-- name    : BookProof.FockNumberPreservingGap.dGamma_shiftCol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T20:28:18.35338+00:00
-- url     : https://prove2.me/theorems/1ef45f3c-7f09-460a-9293-52079f6dde8c
-- title:
--   `BookProof.FockNumberPreservingGap.dGamma_shiftCol` (col : ℕ → (ℕ →₀ ℂ)) (mu : ℝ) (u : FockAlg) : dGamma (shiftCol col mu) u = dGamma col u - ((mu : ℝ) : ℂ) • dGamma numberCol u
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockNumberPreservingGap`.
--
--   `BookProof.FockNumberPreservingGap.dGamma_shiftCol` (col : ℕ → (ℕ →₀ ℂ)) (mu : ℝ) (u : FockAlg) : dGamma (shiftCol col mu) u = dGamma col u - ((mu : ℝ) : ℂ) • dGamma numberCol u
--
--   Formalization note: Lean 4 identifier `BookProof.FockNumberPreservingGap.dGamma_shiftCol`.

-- Generated from ChapterFockNumberPreservingGap.lean — theorem BookProof.FockNumberPreservingGap.dGamma_shiftCol
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.FockNumberPreservingGap


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

theorem BookProof.FockNumberPreservingGap.dGamma_shiftCol (col : ℕ → (ℕ →₀ ℂ)) (mu : ℝ) (u : FockAlg) :
    dGamma (shiftCol col mu) u
      = dGamma col u - ((mu : ℝ) : ℂ) • dGamma numberCol u := by sorry
