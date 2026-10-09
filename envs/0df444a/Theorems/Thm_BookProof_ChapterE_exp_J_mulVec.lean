-- Prove2me | Theorems.Thm_BookProof_ChapterE_exp_J_mulVec
-- name    : BookProof.ChapterE.exp_J_mulVec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T23:09:44.439815+00:00
-- url     : https://prove2.me/theorems/5d1c3138-d2a3-42f1-91e8-1c1319430004
-- title:
--   `BookProof.ChapterE.exp_J_mulVec` (t : ℝ) : (NormedSpace.exp (t • J)) *ᵥ ![1, 0] = Ψ t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterE`.
--
--   `BookProof.ChapterE.exp_J_mulVec` (t : ℝ) : (NormedSpace.exp (t • J)) *ᵥ ![1, 0] = Ψ t
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterE.exp_J_mulVec`.

-- Generated from ChapterE.lean — theorem BookProof.ChapterE.exp_J_mulVec
import Mathlib
import Definitions.Def_ChapterE
open BookProof.ChapterE


open scoped Matrix BigOperators
open Filter
open scoped Topology

theorem BookProof.ChapterE.exp_J_mulVec (t : ℝ) : (NormedSpace.exp (t • J)) *ᵥ ![1, 0] = Ψ t := by sorry
