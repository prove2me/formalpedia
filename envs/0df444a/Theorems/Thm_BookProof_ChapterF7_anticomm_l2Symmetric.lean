-- Prove2me | Theorems.Thm_BookProof_ChapterF7_anticomm_l2Symmetric
-- name    : BookProof.ChapterF7.anticomm_l2Symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T05:06:50.155369+00:00
-- url     : https://prove2.me/theorems/54bf9366-3a55-43dd-8c56-5b81241e73e3
-- title:
--   `BookProof.ChapterF7.anticomm_l2Symmetric` {K V : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)} (hK : IsL2Symmetric K) (hV : IsL2Symmetric V) : IsL2Symmetric (K.comp V + V.comp K)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF7`.
--
--   `BookProof.ChapterF7.anticomm_l2Symmetric` {K V : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)} (hK : IsL2Symmetric K) (hV : IsL2Symmetric V) : IsL2Symmetric (K.comp V + V.comp K)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF7.anticomm_l2Symmetric`.

-- Generated from ChapterF7.lean — theorem BookProof.ChapterF7.anticomm_l2Symmetric
import Mathlib
import Definitions.Def_ChapterF7
open BookProof.ChapterF7


open SchwartzMap MeasureTheory Complex
open scoped BigOperators


noncomputable section

theorem BookProof.ChapterF7.anticomm_l2Symmetric {K V : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)}
    (hK : IsL2Symmetric K) (hV : IsL2Symmetric V) :
    IsL2Symmetric (K.comp V + V.comp K) := by sorry
