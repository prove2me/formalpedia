-- Prove2me | Theorems.Thm_BookProof_SirkSingleTime_sirk_single_time_shiftInvert_bound
-- name    : BookProof.SirkSingleTime.sirk_single_time_shiftInvert_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T02:01:13.133078+00:00
-- url     : https://prove2.me/theorems/4e7c1705-502d-4487-9607-dff1e2fa1dfd
-- title:
--   `BookProof.SirkSingleTime.sirk_single_time_shiftInvert_bound` (A : UnboundedSelfAdjoint E) (l t : ℝ) (V : Fin' →L[ℂ] E) (qX qXinv : E →L[ℂ] E) (qBinv : Fin' →L[ℂ] Fin') (p : Polyno
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSirkSingleTimeShift`.
--
--   `BookProof.SirkSingleTime.sirk_single_time_shiftInvert_bound` (A : UnboundedSelfAdjoint E) (l t : ℝ) (V : Fin' →L[ℂ] E) (qX qXinv : E →L[ℂ] E) (qBinv : Fin' →L[ℂ] Fin') (p : Polynomial ℂ) (psiB : Fin' →L[ℂ] Fin') (C Dmin h : ℝ) (m : ℕ) (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ Fin') (hViso : ∀ x : Fin', ‖V x‖ = ‖x‖) (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖) (hinvX : ∀ x : Fin', ∃ y : Fin', A.resCLM l (V x) = V y) (hinvq : ∀ x : Fin', ∃ y : Fin', qX (V x) = V y) (hqXl : qXinv.comp qX = ContinuousLinearMap.id ℂ E) (hqBr : (compress V qX).comp qBinv = ContinuousLinearMap.id ℂ Fin') (hcx1 : ‖A.stoneU t - (Polynomial.aeval (A.resCLM l) p).comp qXinv‖ ≤ C * (Real.exp (-(h * m)) * Dmin)) (hcx2 : ‖psiB - (Polynomial.aeval (compress V (A.resCLM l)) p).comp qBinv‖ ≤ C * (Real.exp (-(h * m)) * Dmin)) (v : E) (hv : V (V.adjoint v) = v) : ‖A.stoneU t v - sirkApprox V psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m
--
--   Formalization note: Lean 4 identifier `BookProof.SirkSingleTime.sirk_single_time_shiftInvert_bound`.

-- Generated from ChapterSirkSingleTimeShift.lean — theorem BookProof.SirkSingleTime.sirk_single_time_shiftInvert_bound
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterSirkSingleTimeShift
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterSirkEndToEnd
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterQgTimeIndependentFlow
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterSirkEndToEnd
open BookProof.ChapterH4
open BookProof.ChapterH6
open BookProof.ChapterSirkEndToEnd
open BookProof.SirkSingleTime


open scoped InnerProductSpace


open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.HashimotoShiftInvert

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {T : UnboundedSelfAdjoint E} {S : ℕ → UnboundedSelfAdjoint E}
variable {Fin' : Type*} [NormedAddCommGroup Fin'] [InnerProductSpace ℂ Fin'] [CompleteSpace Fin']

theorem BookProof.SirkSingleTime.sirk_single_time_shiftInvert_bound
    (A : UnboundedSelfAdjoint E) (l t : ℝ)
    (V : Fin' →L[ℂ] E) (qX qXinv : E →L[ℂ] E) (qBinv : Fin' →L[ℂ] Fin')
    (p : Polynomial ℂ) (psiB : Fin' →L[ℂ] Fin') (C Dmin h : ℝ) (m : ℕ)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ Fin')
    (hViso : ∀ x : Fin', ‖V x‖ = ‖x‖)
    (hVadj : ∀ v : E, ‖V.adjoint v‖ ≤ ‖v‖)
    (hinvX : ∀ x : Fin', ∃ y : Fin', A.resCLM l (V x) = V y)
    (hinvq : ∀ x : Fin', ∃ y : Fin', qX (V x) = V y)
    (hqXl : qXinv.comp qX = ContinuousLinearMap.id ℂ E)
    (hqBr : (compress V qX).comp qBinv = ContinuousLinearMap.id ℂ Fin')
    (hcx1 : ‖A.stoneU t - (Polynomial.aeval (A.resCLM l) p).comp qXinv‖
      ≤ C * (Real.exp (-(h * m)) * Dmin))
    (hcx2 : ‖psiB - (Polynomial.aeval (compress V (A.resCLM l)) p).comp qBinv‖
      ≤ C * (Real.exp (-(h * m)) * Dmin))
    (v : E) (hv : V (V.adjoint v) = v) :
    ‖A.stoneU t v - sirkApprox V psiB v‖ ≤ sirkBound C Dmin h ‖v‖ m := by sorry
