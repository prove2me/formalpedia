-- Prove2me | Theorems.Thm_BookProof_FockCubicUnbounded_confAt_injective
-- name    : BookProof.FockCubicUnbounded.confAt_injective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:32:52.439526+00:00
-- url     : https://prove2.me/theorems/e3b68aac-860d-4183-a9ff-ed3e1b15e5fc
-- title:
--   `BookProof.FockCubicUnbounded.confAt_injective` (k : ℕ) {m m' : ℕ} (h : confAt k m = confAt k m') : m = m'
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockCubicUnbounded`.
--
--   `BookProof.FockCubicUnbounded.confAt_injective` (k : ℕ) {m m' : ℕ} (h : confAt k m = confAt k m') : m = m'
--
--   Formalization note: Lean 4 identifier `BookProof.FockCubicUnbounded.confAt_injective`.

-- Generated from ChapterFockCubicUnbounded.lean — theorem BookProof.FockCubicUnbounded.confAt_injective
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Mathlib
import Definitions.Def_ChapterFockCubicUnbounded
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization
open BookProof.FockCubicUnbounded


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation

theorem BookProof.FockCubicUnbounded.confAt_injective (k : ℕ) {m m' : ℕ} (h : confAt k m = confAt k m') : m = m' := by sorry
