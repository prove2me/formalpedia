-- Prove2me | Theorems.Thm_BookProof_NsLagrangianDet_ev_conjP
-- name    : BookProof.NsLagrangianDet.ev_conjP
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:55:42.362755+00:00
-- url     : https://prove2.me/theorems/162fe425-fde4-442f-8864-57359384d48b
-- title:
--   `BookProof.NsLagrangianDet.ev_conjP` (y : DIdx K → ℝ) (p : MvPolynomial (DIdx K) ℂ) : ev y (conjP p) = (starRingEnd ℂ) (ev y p)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsLagrangianDetConvolution`.
--
--   `BookProof.NsLagrangianDet.ev_conjP` (y : DIdx K → ℝ) (p : MvPolynomial (DIdx K) ℂ) : ev y (conjP p) = (starRingEnd ℂ) (ev y p)
--
--   Formalization note: Lean 4 identifier `BookProof.NsLagrangianDet.ev_conjP`.

-- Generated from ChapterNsLagrangianDetConvolution.lean — theorem BookProof.NsLagrangianDet.ev_conjP
import Mathlib
import Definitions.Def_ChapterNsLagrangianDetConvolution
open BookProof.NsLagrangianDet



open MvPolynomial Matrix

noncomputable section

variable {K : Type*} [Fintype K]

theorem BookProof.NsLagrangianDet.ev_conjP (y : DIdx K → ℝ) (p : MvPolynomial (DIdx K) ℂ) :
    ev y (conjP p) = (starRingEnd ℂ) (ev y p) := by sorry
