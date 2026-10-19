-- Prove2me | Theorems.Thm_BookProof_ChapterA_qembed_apply
-- name    : BookProof.ChapterA.qembed_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:16:32.766983+00:00
-- url     : https://prove2.me/theorems/593454ea-11e8-4463-9acc-a927ab85ba7e
-- title:
--   `BookProof.ChapterA.qembed_apply` (θ : AntiUnitary V) (hθ : ∀ x, θ (θ x) = -x) (q : Quaternion ℝ) : qembed θ hθ q = algebraMap ℝ (V →L[ℝ] V) q.re + q.imI • mulI + q.imJ • thetaR θ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA2c`.
--
--   `BookProof.ChapterA.qembed_apply` (θ : AntiUnitary V) (hθ : ∀ x, θ (θ x) = -x) (q : Quaternion ℝ) : qembed θ hθ q = algebraMap ℝ (V →L[ℝ] V) q.re + q.imI • mulI + q.imJ • thetaR θ + q.imK • (mulI * thetaR θ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.qembed_apply`.

-- Generated from ChapterA2c.lean — theorem BookProof.ChapterA.qembed_apply
import Mathlib
import Definitions.Def_ChapterA2c
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterA.qembed_apply (θ : AntiUnitary V) (hθ : ∀ x, θ (θ x) = -x) (q : Quaternion ℝ) :
    qembed θ hθ q
      = algebraMap ℝ (V →L[ℝ] V) q.re + q.imI • mulI + q.imJ • thetaR θ
        + q.imK • (mulI * thetaR θ) := by sorry
