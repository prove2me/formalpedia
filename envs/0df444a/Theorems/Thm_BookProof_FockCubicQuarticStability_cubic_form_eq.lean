-- Prove2me | Theorems.Thm_BookProof_FockCubicQuarticStability_cubic_form_eq
-- name    : BookProof.FockCubicQuarticStability.cubic_form_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:46:49.84103+00:00
-- url     : https://prove2.me/theorems/9d856679-0e36-4f44-be16-b643d3d8d974
-- title:
--   `BookProof.FockCubicQuarticStability.cubic_form_eq` (k : ℕ) (u : FockAlg) : (inner ℂ (toLp u) (toLp (cubeA k u)) : ℂ).re = 2 * (inner ℂ (toLp (annA k (annA k u))) (toLp (creA k u))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockCubicQuarticStability`.
--
--   `BookProof.FockCubicQuarticStability.cubic_form_eq` (k : ℕ) (u : FockAlg) : (inner ℂ (toLp u) (toLp (cubeA k u)) : ℂ).re = 2 * (inner ℂ (toLp (annA k (annA k u))) (toLp (creA k u)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.FockCubicQuarticStability.cubic_form_eq`.

-- Generated from ChapterFockCubicQuarticStability.lean — theorem BookProof.FockCubicQuarticStability.cubic_form_eq
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockCubicUnbounded
import Mathlib
import Definitions.Def_ChapterFockCubicQuarticStability
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization
open BookProof.FockCubicQuarticStability


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation
open BookProof.FockCubicUnbounded

theorem BookProof.FockCubicQuarticStability.cubic_form_eq (k : ℕ) (u : FockAlg) :
    (inner ℂ (toLp u) (toLp (cubeA k u)) : ℂ).re
      = 2 * (inner ℂ (toLp (annA k (annA k u))) (toLp (creA k u)) : ℂ).re := by sorry
