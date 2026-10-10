-- Prove2me | Theorems.Thm_BookProof_NsLagrangianDet_conjP_volPot
-- name    : BookProof.NsLagrangianDet.conjP_volPot
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:54:26.646003+00:00
-- url     : https://prove2.me/theorems/96dd3eec-e49e-44d6-9084-ada37398cfa0
-- title:
--   `BookProof.NsLagrangianDet.conjP_volPot` (kappa : ℝ) (kv : K → Fin 3 → ℝ) : conjP (volPot kappa kv) = volPot kappa kv
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsLagrangianDetConvolution`.
--
--   `BookProof.NsLagrangianDet.conjP_volPot` (kappa : ℝ) (kv : K → Fin 3 → ℝ) : conjP (volPot kappa kv) = volPot kappa kv
--
--   Formalization note: Lean 4 identifier `BookProof.NsLagrangianDet.conjP_volPot`.

-- Generated from ChapterNsLagrangianDetConvolution.lean — theorem BookProof.NsLagrangianDet.conjP_volPot
import Mathlib
import Definitions.Def_ChapterNsLagrangianDetConvolution
open BookProof.NsLagrangianDet



open MvPolynomial Matrix

noncomputable section

variable {K : Type*} [Fintype K]

theorem BookProof.NsLagrangianDet.conjP_volPot (kappa : ℝ) (kv : K → Fin 3 → ℝ) :
    conjP (volPot kappa kv) = volPot kappa kv := by sorry
