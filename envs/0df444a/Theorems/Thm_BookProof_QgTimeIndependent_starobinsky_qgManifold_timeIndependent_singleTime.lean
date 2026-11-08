-- Prove2me | Theorems.Thm_BookProof_QgTimeIndependent_starobinsky_qgManifold_timeIndependent_singleTime
-- name    : BookProof.QgTimeIndependent.starobinsky_qgManifold_timeIndependent_singleTime
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-07T23:29:20.561371+00:00
-- url     : https://prove2.me/theorems/0635939a-f7f6-4040-bacd-7d28a99d7acd
-- title:
--   `BookProof.QgTimeIndependent.starobinsky_qgManifold_timeIndependent_singleTime` (M alpha : ℝ) (halpha : 0 < alpha) (Sp : VielbeinSpectrum ι) (g : ℝ) : ∃ (T : UnboundedSelfAdjoint (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgTimeIndependentFlow`.
--
--   `BookProof.QgTimeIndependent.starobinsky_qgManifold_timeIndependent_singleTime` (M alpha : ℝ) (halpha : 0 < alpha) (Sp : VielbeinSpectrum ι) (g : ℝ) : ∃ (T : UnboundedSelfAdjoint (Sec ι)) (S : ℕ → UnboundedSelfAdjoint (Sec ι)), IsSelfAdjointExtension (secHam (starobinskyWall M alpha halpha) (Sp.modes g)) T.op ∧ (∀ n, IsSelfAdjointExtension (secHam (starobinskyWall M alpha halpha) (truncModes (Sp.modes g) (Sp.energyWindow n))) (S n).op) ∧ (∀ t s : ℝ, prop T t s = T.stoneU (t - s)) ∧ (∀ (t s : ℝ) (x : Sec ι), ‖prop T t s x‖ = ‖x‖) ∧ (∀ (t s r : ℝ) (x : Sec ι), prop T t s (prop T s r x) = prop T t r x) ∧ (∀ t s h : ℝ, prop T (t + h) (s + h) = prop T t s) ∧ (∀ y : ℝ → Sec ι, IsSchrodingerSolution T y → ∀ t s : ℝ, y t = prop T t s (y s)) ∧ (∀ l : ℝ, l ≠ 0 → IsShiftInvertC T.op (((l : ℝ) : ℂ) * Complex.I) (-(T.resCLM l)) ∧ (∀ n, IsShiftInvertC (S n).op (((l : ℝ) : ℂ) * Complex.I) (-((S n).resCLM l))) ∧ ∀ u : Sec ι, Tendsto (fun n => -((S n).resCLM l u)) atTop (𝓝 (-(T.resCLM l u)))) ∧ ∀ (v : Sec ι) (t : ℝ), Tendsto (fun n => (S n).stoneU t v) atTop (𝓝 (T.stoneU t v))
--
--   Formalization note: Lean 4 identifier `BookProof.QgTimeIndependent.starobinsky_qgManifold_timeIndependent_singleTime`.

-- Generated from ChapterQgTimeIndependentFlow.lean — theorem BookProof.QgTimeIndependent.starobinsky_qgManifold_timeIndependent_singleTime
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterQgTimeIndependentFlowPromoted
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHashimotoComplexShifts
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterQgTimeIndependentFlowPromoted
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterSirkBandLedger
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterQgManifoldModeInstance
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterQgTruncationResolvent
open BookProof.EsaClosure
open BookProof.FockSecondQuantization
open BookProof.HashimotoShiftInvert
open BookProof.QgTimeIndependent
open BookProof.ScalaronOuterFockFL
open BookProof.QgManifoldModeInstance
open BookProof.ScalaronFiberFL
open BookProof.QgTruncationResolvent



open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {ι : Type*}

theorem BookProof.QgTimeIndependent.starobinsky_qgManifold_timeIndependent_singleTime (M alpha : ℝ)
    (halpha : 0 < alpha) (Sp : VielbeinSpectrum ι) (g : ℝ) :
    ∃ (T : UnboundedSelfAdjoint (Sec ι)) (S : ℕ → UnboundedSelfAdjoint (Sec ι)),
      IsSelfAdjointExtension (secHam (starobinskyWall M alpha halpha) (Sp.modes g)) T.op ∧
        (∀ n, IsSelfAdjointExtension (secHam (starobinskyWall M alpha halpha)
          (truncModes (Sp.modes g) (Sp.energyWindow n))) (S n).op) ∧
        (∀ t s : ℝ, prop T t s = T.stoneU (t - s)) ∧
        (∀ (t s : ℝ) (x : Sec ι), ‖prop T t s x‖ = ‖x‖) ∧
        (∀ (t s r : ℝ) (x : Sec ι), prop T t s (prop T s r x) = prop T t r x) ∧
        (∀ t s h : ℝ, prop T (t + h) (s + h) = prop T t s) ∧
        (∀ y : ℝ → Sec ι, IsSchrodingerSolution T y → ∀ t s : ℝ, y t = prop T t s (y s)) ∧
        (∀ l : ℝ, l ≠ 0 →
          IsShiftInvertC T.op (((l : ℝ) : ℂ) * Complex.I) (-(T.resCLM l)) ∧
            (∀ n, IsShiftInvertC (S n).op (((l : ℝ) : ℂ) * Complex.I) (-((S n).resCLM l))) ∧
            ∀ u : Sec ι,
              Tendsto (fun n => -((S n).resCLM l u)) atTop (𝓝 (-(T.resCLM l u)))) ∧
        ∀ (v : Sec ι) (t : ℝ),
          Tendsto (fun n => (S n).stoneU t v) atTop (𝓝 (T.stoneU t v)) := by sorry
