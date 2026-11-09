-- Prove2me | Theorems.Thm_BookProof_QgTimeIndependent_hasDerivAt_prop
-- name    : BookProof.QgTimeIndependent.hasDerivAt_prop
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T23:28:53.478524+00:00
-- url     : https://prove2.me/theorems/e4c0bffd-5ec6-4223-b687-010ef9e0540e
-- title:
--   `BookProof.QgTimeIndependent.hasDerivAt_prop` (T : UnboundedSelfAdjoint E) (x : T.domain) (t s : ℝ) : HasDerivAt (fun r : ℝ => prop T r s (x : E)) ((-Complex.I) • T.op ⟨T.stoneU (t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgTimeIndependentFlow`.
--
--   `BookProof.QgTimeIndependent.hasDerivAt_prop` (T : UnboundedSelfAdjoint E) (x : T.domain) (t s : ℝ) : HasDerivAt (fun r : ℝ => prop T r s (x : E)) ((-Complex.I) • T.op ⟨T.stoneU (t - s) (x : E), T.stoneU_mem_domain (t - s) x⟩) t
--
--   Formalization note: Lean 4 identifier `BookProof.QgTimeIndependent.hasDerivAt_prop`.

-- Generated from ChapterQgTimeIndependentFlow.lean — theorem BookProof.QgTimeIndependent.hasDerivAt_prop
import Mathlib
import Definitions.Def_ChapterQgTimeIndependentFlowPromoted
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
open BookProof.ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent
open BookProof.QgTimeIndependent



open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.QgTimeIndependent.hasDerivAt_prop (T : UnboundedSelfAdjoint E) (x : T.domain) (t s : ℝ) :
    HasDerivAt (fun r : ℝ => prop T r s (x : E))
      ((-Complex.I) • T.op ⟨T.stoneU (t - s) (x : E), T.stoneU_mem_domain (t - s) x⟩) t := by sorry
