-- Prove2me | Theorems.Thm_BookProof_ChapterF7_smul_l2Symmetric
-- name    : BookProof.ChapterF7.smul_l2Symmetric
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T05:06:51.329597+00:00
-- url     : https://prove2.me/theorems/eb4867e4-b02c-4852-a051-1c8690f9716a
-- title:
--   `BookProof.ChapterF7.smul_l2Symmetric` {c : ℂ} (hc : (starRingEnd ℂ) c = c) {T : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)} (hT : IsL2Symmetric T) : IsL2Symmetric (c • T)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF7`.
--
--   `BookProof.ChapterF7.smul_l2Symmetric` {c : ℂ} (hc : (starRingEnd ℂ) c = c) {T : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)} (hT : IsL2Symmetric T) : IsL2Symmetric (c • T)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF7.smul_l2Symmetric`.

-- Generated from ChapterF7.lean — theorem BookProof.ChapterF7.smul_l2Symmetric
import Mathlib
import Definitions.Def_ChapterF7
open BookProof.ChapterF7


open SchwartzMap MeasureTheory Complex
open scoped BigOperators


noncomputable section

theorem BookProof.ChapterF7.smul_l2Symmetric {c : ℂ} (hc : (starRingEnd ℂ) c = c)
    {T : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)} (hT : IsL2Symmetric T) :
    IsL2Symmetric (c • T) := by sorry
