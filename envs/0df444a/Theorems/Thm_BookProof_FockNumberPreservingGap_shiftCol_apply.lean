-- Prove2me | Theorems.Thm_BookProof_FockNumberPreservingGap_shiftCol_apply
-- name    : BookProof.FockNumberPreservingGap.shiftCol_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T20:26:34.948201+00:00
-- url     : https://prove2.me/theorems/97918e5e-31d6-4e5b-8997-ce80be51b765
-- title:
--   `BookProof.FockNumberPreservingGap.shiftCol_apply` (col : ℕ → (ℕ →₀ ℂ)) (mu : ℝ) (k : ℕ) : shiftCol col mu k = col k - ((mu : ℝ) : ℂ) • numberCol k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockNumberPreservingGap`.
--
--   `BookProof.FockNumberPreservingGap.shiftCol_apply` (col : ℕ → (ℕ →₀ ℂ)) (mu : ℝ) (k : ℕ) : shiftCol col mu k = col k - ((mu : ℝ) : ℂ) • numberCol k
--
--   Formalization note: Lean 4 identifier `BookProof.FockNumberPreservingGap.shiftCol_apply`.

-- Generated from ChapterFockNumberPreservingGap.lean — theorem BookProof.FockNumberPreservingGap.shiftCol_apply
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

theorem BookProof.FockNumberPreservingGap.shiftCol_apply (col : ℕ → (ℕ →₀ ℂ)) (mu : ℝ) (k : ℕ) :
    shiftCol col mu k = col k - ((mu : ℝ) : ℂ) • numberCol k := by sorry
