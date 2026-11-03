-- Prove2me | Theorems.Thm_BookProof_SirkSingleTime_starobinsky_qgManifold_singleTime_shiftInvert_convergence
-- name    : BookProof.SirkSingleTime.starobinsky_qgManifold_singleTime_shiftInvert_convergence
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-02T11:18:45.203634+00:00
-- url     : https://prove2.me/theorems/7d1e65a1-eafb-4b4c-92d4-160e058e26b3
-- title:
--   `BookProof.SirkSingleTime.starobinsky_qgManifold_singleTime_shiftInvert_convergence` (M alpha : ℝ) (halpha : 0 < alpha) (Sp : VielbeinSpectrum ι) (g : ℝ) : ∃ (T : UnboundedSelfAdjo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSirkSingleTimeShift`.
--
--   `BookProof.SirkSingleTime.starobinsky_qgManifold_singleTime_shiftInvert_convergence` (M alpha : ℝ) (halpha : 0 < alpha) (Sp : VielbeinSpectrum ι) (g : ℝ) : ∃ (T : UnboundedSelfAdjoint (Sec ι)) (Sn : ℕ → UnboundedSelfAdjoint (Sec ι)), IsSelfAdjointExtension (secHam (starobinskyWall M alpha halpha) (Sp.modes g)) T.op ∧ (∀ n, IsSelfAdjointExtension (secHam (starobinskyWall M alpha halpha) (truncModes (Sp.modes g) (Sp.energyWindow n))) (Sn n).op) ∧ (∀ l : ℝ, l ≠ 0 → IsShiftInvertC T.op (((l : ℝ) : ℂ) * Complex.I) (-(T.resCLM l)) ∧ (∀ n, IsShiftInvertC (Sn n).op (((l : ℝ) : ℂ) * Complex.I) (-((Sn n).resCLM l))) ∧ ∀ u : Sec ι, Tendsto (fun n => -((Sn n).resCLM l u)) atTop (𝓝 (-(T.resCLM l u)))) ∧ ∀ (v : Sec ι) (t : ℝ), Tendsto (fun n => (Sn n).stoneU t v) atTop (𝓝 (T.stoneU t v))
--
--   Formalization note: Lean 4 identifier `BookProof.SirkSingleTime.starobinsky_qgManifold_singleTime_shiftInvert_convergence`.

-- Generated from ChapterSirkSingleTimeShift.lean — theorem BookProof.SirkSingleTime.starobinsky_qgManifold_singleTime_shiftInvert_convergence
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterSirkSingleTimeShift
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHashimotoComplexShifts
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterQgTimeIndependentFlow
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterSirkBandLedger
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterQgTruncationResolvent
import Definitions.Def_ChapterQgManifoldModeInstance
open BookProof.EsaClosure
open BookProof.FockSecondQuantization
open BookProof.HashimotoShiftInvert
open BookProof.SirkSingleTime
open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgTruncationResolvent
open BookProof.QgManifoldModeInstance


open scoped InnerProductSpace


open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.HashimotoShiftInvert

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {T : UnboundedSelfAdjoint E} {S : ℕ → UnboundedSelfAdjoint E}
variable {Fin' : Type*} [NormedAddCommGroup Fin'] [InnerProductSpace ℂ Fin'] [CompleteSpace Fin']
variable {ι : Type*}

theorem BookProof.SirkSingleTime.starobinsky_qgManifold_singleTime_shiftInvert_convergence (M alpha : ℝ)
    (halpha : 0 < alpha) (Sp : VielbeinSpectrum ι) (g : ℝ) :
    ∃ (T : UnboundedSelfAdjoint (Sec ι)) (Sn : ℕ → UnboundedSelfAdjoint (Sec ι)),
      IsSelfAdjointExtension (secHam (starobinskyWall M alpha halpha) (Sp.modes g)) T.op ∧
        (∀ n, IsSelfAdjointExtension (secHam (starobinskyWall M alpha halpha)
          (truncModes (Sp.modes g) (Sp.energyWindow n))) (Sn n).op) ∧
        (∀ l : ℝ, l ≠ 0 →
          IsShiftInvertC T.op (((l : ℝ) : ℂ) * Complex.I) (-(T.resCLM l)) ∧
            (∀ n, IsShiftInvertC (Sn n).op (((l : ℝ) : ℂ) * Complex.I) (-((Sn n).resCLM l))) ∧
            ∀ u : Sec ι,
              Tendsto (fun n => -((Sn n).resCLM l u)) atTop (𝓝 (-(T.resCLM l u)))) ∧
        ∀ (v : Sec ι) (t : ℝ),
          Tendsto (fun n => (Sn n).stoneU t v) atTop (𝓝 (T.stoneU t v)) := by sorry
