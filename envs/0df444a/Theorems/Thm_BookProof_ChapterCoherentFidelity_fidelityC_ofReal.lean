-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentFidelity_fidelityC_ofReal
-- name    : BookProof.ChapterCoherentFidelity.fidelityC_ofReal
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:51:55.895986+00:00
-- url     : https://prove2.me/theorems/43a77ef5-e89e-4222-b647-4c44e3a85d3e
-- title:
--   `BookProof.ChapterCoherentFidelity.fidelityC_ofReal` (q k : EuclideanSpace ℝ (Fin n)) : fidelityC (ofRealVec q) (ofRealVec k) = Real.exp (-‖q - k‖ ^ 2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentFidelity`.
--
--   `BookProof.ChapterCoherentFidelity.fidelityC_ofReal` (q k : EuclideanSpace ℝ (Fin n)) : fidelityC (ofRealVec q) (ofRealVec k) = Real.exp (-‖q - k‖ ^ 2)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentFidelity.fidelityC_ofReal`.

-- Generated from ChapterCoherentFidelity.lean — theorem BookProof.ChapterCoherentFidelity.fidelityC_ofReal
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterCoherentFidelity
import Definitions.Def_ChapterCoherentOverlapComplex
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterCoherentOverlapComplex
open BookProof.ChapterSoftmaxBorn
open BookProof.ChapterCoherentFidelity


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterSoftmaxSharpness

variable {n m : ℕ}

theorem BookProof.ChapterCoherentFidelity.fidelityC_ofReal (q k : EuclideanSpace ℝ (Fin n)) :
    fidelityC (ofRealVec q) (ofRealVec k) = Real.exp (-‖q - k‖ ^ 2) := by sorry
