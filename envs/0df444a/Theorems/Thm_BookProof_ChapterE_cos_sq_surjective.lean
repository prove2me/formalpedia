-- Prove2me | Theorems.Thm_BookProof_ChapterE_cos_sq_surjective
-- name    : BookProof.ChapterE.cos_sq_surjective
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:09:28.534357+00:00
-- url     : https://prove2.me/theorems/66a51da0-22b1-4f4e-9c70-dc6d808bcd8d
-- title:
--   `BookProof.ChapterE.cos_sq_surjective` {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ∃ t : ℝ, Real.cos t ^ 2 = p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterE`.
--
--   `BookProof.ChapterE.cos_sq_surjective` {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ∃ t : ℝ, Real.cos t ^ 2 = p
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterE.cos_sq_surjective`.

-- Generated from ChapterE.lean — theorem BookProof.ChapterE.cos_sq_surjective
import Mathlib
import Definitions.Def_ChapterE
open BookProof.ChapterE


open scoped Matrix BigOperators
open Filter
open scoped Topology

theorem BookProof.ChapterE.cos_sq_surjective {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ t : ℝ, Real.cos t ^ 2 = p := by sorry
