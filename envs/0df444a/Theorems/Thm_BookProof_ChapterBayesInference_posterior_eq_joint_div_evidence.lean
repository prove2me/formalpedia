-- Prove2me | Theorems.Thm_BookProof_ChapterBayesInference_posterior_eq_joint_div_evidence
-- name    : BookProof.ChapterBayesInference.posterior_eq_joint_div_evidence
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:53:23.449968+00:00
-- url     : https://prove2.me/theorems/5e354b47-c0aa-4d5f-96d3-1b64c1dd066f
-- title:
--   `BookProof.ChapterBayesInference.posterior_eq_joint_div_evidence` (y : Y) (x : X) : posterior prior L y x = joint prior L x y / evidence prior L y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBayesInference`.
--
--   `BookProof.ChapterBayesInference.posterior_eq_joint_div_evidence` (y : Y) (x : X) : posterior prior L y x = joint prior L x y / evidence prior L y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBayesInference.posterior_eq_joint_div_evidence`.

-- Generated from ChapterBayesInference.lean — theorem BookProof.ChapterBayesInference.posterior_eq_joint_div_evidence
import Mathlib
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference


open scoped BigOperators


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

variable {prior : X → ℝ} {L : X → Y → ℝ}

theorem BookProof.ChapterBayesInference.posterior_eq_joint_div_evidence (y : Y) (x : X) :
    posterior prior L y x = joint prior L x y / evidence prior L y := by sorry
