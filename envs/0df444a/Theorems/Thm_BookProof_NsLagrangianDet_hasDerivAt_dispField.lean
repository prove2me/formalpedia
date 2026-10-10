-- Prove2me | Theorems.Thm_BookProof_NsLagrangianDet_hasDerivAt_dispField
-- name    : BookProof.NsLagrangianDet.hasDerivAt_dispField
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:55:25.733205+00:00
-- url     : https://prove2.me/theorems/5dc8fa3d-7d7c-4db9-9981-bc4ac4d71c6d
-- title:
--   `BookProof.NsLagrangianDet.hasDerivAt_dispField` (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) (a : Fin 3 → ℝ) (r c : Fin 3) : HasDerivAt (fun t : ℝ => dispField kv y (a + t • (Pi.single c
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsLagrangianDetConvolution`.
--
--   `BookProof.NsLagrangianDet.hasDerivAt_dispField` (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) (a : Fin 3 → ℝ) (r c : Fin 3) : HasDerivAt (fun t : ℝ => dispField kv y (a + t • (Pi.single c (1 : ℝ) : Fin 3 → ℝ)) r) (dispGrad kv y a r c) 0
--
--   Formalization note: Lean 4 identifier `BookProof.NsLagrangianDet.hasDerivAt_dispField`.

-- Generated from ChapterNsLagrangianDetConvolution.lean — theorem BookProof.NsLagrangianDet.hasDerivAt_dispField
import Mathlib
import Definitions.Def_ChapterNsLagrangianDetConvolution
open BookProof.NsLagrangianDet



open MvPolynomial Matrix

noncomputable section

variable {K : Type*} [Fintype K]

theorem BookProof.NsLagrangianDet.hasDerivAt_dispField (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) (a : Fin 3 → ℝ)
    (r c : Fin 3) :
    HasDerivAt (fun t : ℝ => dispField kv y (a + t • (Pi.single c (1 : ℝ) : Fin 3 → ℝ)) r)
      (dispGrad kv y a r c) 0 := by sorry
