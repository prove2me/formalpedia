-- Prove2me | Theorems.Thm_BookProof_ChapterE_exp_J
-- name    : BookProof.ChapterE.exp_J
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:09:36.955882+00:00
-- url     : https://prove2.me/theorems/fbd616e1-715a-4c41-9ae4-251252e0c0ac
-- title:
--   `BookProof.ChapterE.exp_J` (t : ℝ) : NormedSpace.exp (t • J) = !![Real.cos t, -Real.sin t; Real.sin t, Real.cos t]
-- statement:
--   Prove the following Lean 4 theorem from `ChapterE`.
--
--   `BookProof.ChapterE.exp_J` (t : ℝ) : NormedSpace.exp (t • J) = !![Real.cos t, -Real.sin t; Real.sin t, Real.cos t]
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterE.exp_J`.

-- Generated from ChapterE.lean — theorem BookProof.ChapterE.exp_J
import Mathlib
import Definitions.Def_ChapterE
open BookProof.ChapterE


open scoped Matrix BigOperators
open Filter
open scoped Topology

theorem BookProof.ChapterE.exp_J (t : ℝ) :
    NormedSpace.exp (t • J) = !![Real.cos t, -Real.sin t; Real.sin t, Real.cos t] := by sorry
