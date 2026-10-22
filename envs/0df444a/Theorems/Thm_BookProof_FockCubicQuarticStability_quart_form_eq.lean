-- Prove2me | Theorems.Thm_BookProof_FockCubicQuarticStability_quart_form_eq
-- name    : BookProof.FockCubicQuarticStability.quart_form_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:46:49.370719+00:00
-- url     : https://prove2.me/theorems/432fee17-1a6e-46ee-a04e-10902e25a096
-- title:
--   `BookProof.FockCubicQuarticStability.quart_form_eq` (k : ℕ) (u : FockAlg) : (inner ℂ (toLp u) (toLp (quartA k u)) : ℂ).re = ‖toLp (annA k (annA k u))‖ ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockCubicQuarticStability`.
--
--   `BookProof.FockCubicQuarticStability.quart_form_eq` (k : ℕ) (u : FockAlg) : (inner ℂ (toLp u) (toLp (quartA k u)) : ℂ).re = ‖toLp (annA k (annA k u))‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.FockCubicQuarticStability.quart_form_eq`.

-- Generated from ChapterFockCubicQuarticStability.lean — theorem BookProof.FockCubicQuarticStability.quart_form_eq
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

theorem BookProof.FockCubicQuarticStability.quart_form_eq (k : ℕ) (u : FockAlg) :
    (inner ℂ (toLp u) (toLp (quartA k u)) : ℂ).re = ‖toLp (annA k (annA k u))‖ ^ 2 := by sorry
