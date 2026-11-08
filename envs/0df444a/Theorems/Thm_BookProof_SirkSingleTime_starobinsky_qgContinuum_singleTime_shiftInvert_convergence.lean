-- Prove2me | Theorems.Thm_BookProof_SirkSingleTime_starobinsky_qgContinuum_singleTime_shiftInvert_convergence
-- name    : BookProof.SirkSingleTime.starobinsky_qgContinuum_singleTime_shiftInvert_convergence
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T00:25:30.456275+00:00
-- url     : https://prove2.me/theorems/2fffa7b4-c59b-4706-be6a-874ccac95f69
-- title:
--   `BookProof.SirkSingleTime.starobinsky_qgContinuum_singleTime_shiftInvert_convergence` (M alpha : ℝ) (halpha : 0 < alpha) (g : ℝ) : ∃ (T : UnboundedSelfAdjoint (Sec CMode)) (S : ℕ →
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSirkSingleTimeShift`.
--
--   `BookProof.SirkSingleTime.starobinsky_qgContinuum_singleTime_shiftInvert_convergence` (M alpha : ℝ) (halpha : 0 < alpha) (g : ℝ) : ∃ (T : UnboundedSelfAdjoint (Sec CMode)) (S : ℕ → UnboundedSelfAdjoint (Sec CMode)), IsSelfAdjointExtension (secHam (starobinskyWall M alpha halpha) (qgContinuumModes g)) T.op ∧ (∀ n, IsSelfAdjointExtension (secHam (starobinskyWall M alpha halpha) (truncModes (qgContinuumModes g) (momWindow n))) (S n).op) ∧ (∀ l : ℝ, l ≠ 0 → IsShiftInvertC T.op (((l : ℝ) : ℂ) * Complex.I) (-(T.resCLM l)) ∧ (∀ n, IsShiftInvertC (S n).op (((l : ℝ) : ℂ) * Complex.I) (-((S n).resCLM l))) ∧ ∀ u : Sec CMode, Tendsto (fun n => -((S n).resCLM l u)) atTop (𝓝 (-(T.resCLM l u)))) ∧ ∀ (v : Sec CMode) (t : ℝ), Tendsto (fun n => (S n).stoneU t v) atTop (𝓝 (T.stoneU t v))
--
--   Formalization note: Lean 4 identifier `BookProof.SirkSingleTime.starobinsky_qgContinuum_singleTime_shiftInvert_convergence`.

-- Generated from ChapterSirkSingleTimeShift.lean — theorem BookProof.SirkSingleTime.starobinsky_qgContinuum_singleTime_shiftInvert_convergence
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterSirkSingleTimeShift
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterHashimotoComplexShifts
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterQgTimeIndependentFlowPromoted
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterQgTruncationResolvent
import Definitions.Def_ChapterQgBrstDerivativeGauge
import Definitions.Def_ChapterQgContinuumModeInstance
open BookProof.EsaClosure
open BookProof.HashimotoShiftInvert
open BookProof.SirkSingleTime
open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgTruncationResolvent
open BookProof.QgBrstDerivativeGauge
open BookProof.QgContinuumModeInstance


open scoped InnerProductSpace


open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.HashimotoShiftInvert

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {T : UnboundedSelfAdjoint E} {S : ℕ → UnboundedSelfAdjoint E}
variable {Fin' : Type*} [NormedAddCommGroup Fin'] [InnerProductSpace ℂ Fin'] [CompleteSpace Fin']
variable {ι : Type*}

theorem BookProof.SirkSingleTime.starobinsky_qgContinuum_singleTime_shiftInvert_convergence (M alpha : ℝ)
    (halpha : 0 < alpha) (g : ℝ) :
    ∃ (T : UnboundedSelfAdjoint (Sec CMode)) (S : ℕ → UnboundedSelfAdjoint (Sec CMode)),
      IsSelfAdjointExtension
          (secHam (starobinskyWall M alpha halpha) (qgContinuumModes g)) T.op ∧
        (∀ n, IsSelfAdjointExtension (secHam (starobinskyWall M alpha halpha)
          (truncModes (qgContinuumModes g) (momWindow n))) (S n).op) ∧
        (∀ l : ℝ, l ≠ 0 →
          IsShiftInvertC T.op (((l : ℝ) : ℂ) * Complex.I) (-(T.resCLM l)) ∧
            (∀ n, IsShiftInvertC (S n).op (((l : ℝ) : ℂ) * Complex.I) (-((S n).resCLM l))) ∧
            ∀ u : Sec CMode,
              Tendsto (fun n => -((S n).resCLM l u)) atTop (𝓝 (-(T.resCLM l u)))) ∧
        ∀ (v : Sec CMode) (t : ℝ),
          Tendsto (fun n => (S n).stoneU t v) atTop (𝓝 (T.stoneU t v)) := by sorry
