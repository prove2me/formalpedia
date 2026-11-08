-- Prove2me | Theorems.Thm_BookProof_QgTimeIndependent_starobinsky_brstGaugeFixed_timeIndependent_singleTime
-- name    : BookProof.QgTimeIndependent.starobinsky_brstGaugeFixed_timeIndependent_singleTime
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-07T23:28:36.922593+00:00
-- url     : https://prove2.me/theorems/d0931fe0-a45e-4b65-ad29-c9714f35df0c
-- title:
--   `BookProof.QgTimeIndependent.starobinsky_brstGaugeFixed_timeIndependent_singleTime` (M alpha : ℝ) (halpha : 0 < alpha) (g : ℝ) : ∃ (T : UnboundedSelfAdjoint (Sec CMode)) (S : ℕ → U
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgTimeIndependentFlow`.
--
--   `BookProof.QgTimeIndependent.starobinsky_brstGaugeFixed_timeIndependent_singleTime` (M alpha : ℝ) (halpha : 0 < alpha) (g : ℝ) : ∃ (T : UnboundedSelfAdjoint (Sec CMode)) (S : ℕ → UnboundedSelfAdjoint (Sec CMode)), (∀ x y : CMode, x.1 = y.1 → ∑ mu : Fin 3, ∑ nu : Fin 3, ∑ i : Fin 3, (starRingEnd ℂ) (gaugeReduce (extTorsionCoef x.1 mu nu i) x) * gaugeReduce (extTorsionCoef x.1 mu nu i) y = contTorsionGram x y) ∧ IsSelfAdjointExtension (secHam (starobinskyWall M alpha halpha) (qgContinuumModes g)) T.op ∧ (∀ n, IsSelfAdjointExtension (secHam (starobinskyWall M alpha halpha) (truncModes (qgContinuumModes g) (momWindow n))) (S n).op) ∧ (∀ t s : ℝ, prop T t s = T.stoneU (t - s)) ∧ (∀ (t s : ℝ) (x : Sec CMode), ‖prop T t s x‖ = ‖x‖) ∧ (∀ (t s r : ℝ) (x : Sec CMode), prop T t s (prop T s r x) = prop T t r x) ∧ (∀ t s h : ℝ, prop T (t + h) (s + h) = prop T t s) ∧ (∀ y : ℝ → Sec CMode, IsSchrodingerSolution T y → ∀ t s : ℝ, y t = prop T t s (y s)) ∧ (∀ l : ℝ, l ≠ 0 → IsShiftInvertC T.op (((l : ℝ) : ℂ) * Complex.I) (-(T.resCLM l)) ∧ (∀ n, IsShiftInvertC (S n).op (((l : ℝ) : ℂ) * Complex.I) (-((S n).resCLM l))) ∧ ∀ u : Sec CMode, Tendsto (fun n => -((S n).resCLM l u)) atTop (𝓝 (-(T.resCLM l u)))) ∧ ∀ (v : Sec CMode) (t : ℝ), Tendsto (fun n => (S n).stoneU t v) atTop (𝓝 (T.stoneU t v))
--
--   Formalization note: Lean 4 identifier `BookProof.QgTimeIndependent.starobinsky_brstGaugeFixed_timeIndependent_singleTime`.

-- Generated from ChapterQgTimeIndependentFlow.lean — theorem BookProof.QgTimeIndependent.starobinsky_brstGaugeFixed_timeIndependent_singleTime
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterQgTimeIndependentFlowPromoted
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterHashimotoComplexShifts
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterQgTimeIndependentFlowPromoted
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterQgContinuumModeInstance
import Definitions.Def_ChapterQgBrstDerivativeGaugeV2
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterQgTruncationResolvent
open BookProof.EsaClosure
open BookProof.HashimotoShiftInvert
open BookProof.QgTimeIndependent
open BookProof.ScalaronOuterFockFL
open BookProof.QgContinuumModeInstance BookProof.QgBrstDerivativeGauge
open BookProof.ScalaronFiberFL
open BookProof.QgTruncationResolvent



open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {ι : Type*}

theorem BookProof.QgTimeIndependent.starobinsky_brstGaugeFixed_timeIndependent_singleTime (M alpha : ℝ)
    (halpha : 0 < alpha) (g : ℝ) :
    ∃ (T : UnboundedSelfAdjoint (Sec CMode)) (S : ℕ → UnboundedSelfAdjoint (Sec CMode)),
      (∀ x y : CMode, x.1 = y.1 →
          ∑ mu : Fin 3, ∑ nu : Fin 3, ∑ i : Fin 3,
              (starRingEnd ℂ) (gaugeReduce (extTorsionCoef x.1 mu nu i) x)
                * gaugeReduce (extTorsionCoef x.1 mu nu i) y
            = contTorsionGram x y) ∧
      IsSelfAdjointExtension
          (secHam (starobinskyWall M alpha halpha) (qgContinuumModes g)) T.op ∧
        (∀ n, IsSelfAdjointExtension (secHam (starobinskyWall M alpha halpha)
          (truncModes (qgContinuumModes g) (momWindow n))) (S n).op) ∧
        (∀ t s : ℝ, prop T t s = T.stoneU (t - s)) ∧
        (∀ (t s : ℝ) (x : Sec CMode), ‖prop T t s x‖ = ‖x‖) ∧
        (∀ (t s r : ℝ) (x : Sec CMode), prop T t s (prop T s r x) = prop T t r x) ∧
        (∀ t s h : ℝ, prop T (t + h) (s + h) = prop T t s) ∧
        (∀ y : ℝ → Sec CMode, IsSchrodingerSolution T y → ∀ t s : ℝ, y t = prop T t s (y s)) ∧
        (∀ l : ℝ, l ≠ 0 →
          IsShiftInvertC T.op (((l : ℝ) : ℂ) * Complex.I) (-(T.resCLM l)) ∧
            (∀ n, IsShiftInvertC (S n).op (((l : ℝ) : ℂ) * Complex.I) (-((S n).resCLM l))) ∧
            ∀ u : Sec CMode,
              Tendsto (fun n => -((S n).resCLM l u)) atTop (𝓝 (-(T.resCLM l u)))) ∧
        ∀ (v : Sec CMode) (t : ℝ),
          Tendsto (fun n => (S n).stoneU t v) atTop (𝓝 (T.stoneU t v)) := by sorry
