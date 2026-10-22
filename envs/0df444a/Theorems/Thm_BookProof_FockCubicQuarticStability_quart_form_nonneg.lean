-- Prove2me | Theorems.Thm_BookProof_FockCubicQuarticStability_quart_form_nonneg
-- name    : BookProof.FockCubicQuarticStability.quart_form_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:46:44.660993+00:00
-- url     : https://prove2.me/theorems/e9cc9236-4dbf-4065-9f4a-9d904a32e10d
-- title:
--   `BookProof.FockCubicQuarticStability.quart_form_nonneg` (k : ℕ) (u : FockAlg) : 0 ≤ (inner ℂ (toLp u) (toLp (quartA k u)) : ℂ).re
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockCubicQuarticStability`.
--
--   `BookProof.FockCubicQuarticStability.quart_form_nonneg` (k : ℕ) (u : FockAlg) : 0 ≤ (inner ℂ (toLp u) (toLp (quartA k u)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.FockCubicQuarticStability.quart_form_nonneg`.

-- Generated from ChapterFockCubicQuarticStability.lean — theorem BookProof.FockCubicQuarticStability.quart_form_nonneg
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

theorem BookProof.FockCubicQuarticStability.quart_form_nonneg (k : ℕ) (u : FockAlg) :
    0 ≤ (inner ℂ (toLp u) (toLp (quartA k u)) : ℂ).re := by sorry
