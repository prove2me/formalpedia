-- Prove2me | Theorems.Thm_BookProof_QgTruncationResolvent_starobinsky_qgContinuum_momentumCutoff_flow_convergence
-- name    : BookProof.QgTruncationResolvent.starobinsky_qgContinuum_momentumCutoff_flow_convergence
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T22:57:24.851598+00:00
-- url     : https://prove2.me/theorems/f1f2c35e-b842-4eea-b842-07d907199701
-- title:
--   `BookProof.QgTruncationResolvent.starobinsky_qgContinuum_momentumCutoff_flow_convergence` (M alpha : ℝ) (halpha : 0 < alpha) (g : ℝ) : ∃ (T : UnboundedSelfAdjoint (Sec CMode)) (S :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgTruncationResolvent`.
--
--   `BookProof.QgTruncationResolvent.starobinsky_qgContinuum_momentumCutoff_flow_convergence` (M alpha : ℝ) (halpha : 0 < alpha) (g : ℝ) : ∃ (T : UnboundedSelfAdjoint (Sec CMode)) (S : ℕ → UnboundedSelfAdjoint (Sec CMode)), IsSelfAdjointExtension (secHam (starobinskyWall M alpha halpha) (qgContinuumModes g)) T.op ∧ (∀ n, IsSelfAdjointExtension (secHam (starobinskyWall M alpha halpha) (truncModes (qgContinuumModes g) (momWindow n))) (S n).op) ∧ StrongResolventConvergence T S ∧ ∀ (v : Sec CMode) (T₀ : ℝ), 0 ≤ T₀ → TendstoUniformlyOn (fun n t => (S n).stoneU t v) (fun t => T.stoneU t v) atTop (Set.Icc (-T₀) T₀) ∧ ∀ t : ℝ, Tendsto (fun n => (S n).stoneU t v) atTop (𝓝 (T.stoneU t v))
--
--   Formalization note: Lean 4 identifier `BookProof.QgTruncationResolvent.starobinsky_qgContinuum_momentumCutoff_flow_convergence`.

-- Generated from ChapterQgTruncationResolvent.lean — theorem BookProof.QgTruncationResolvent.starobinsky_qgContinuum_momentumCutoff_flow_convergence
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterDirectSumEsa
import Mathlib
import Definitions.Def_ChapterQgTruncationResolvent
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterQgTimeIndependentFlow
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterQgContinuumModeInstance
open BookProof.EsaClosure
open BookProof.ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent
open BookProof.QgTruncationResolvent



open Filter Topology
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.QgOuterFockCoreFL BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.ScalaronEsa BookProof.DirectSumEsa
open BookProof.QgContinuumModeInstance

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {ι : Type*}
variable (W : WallPot) (Q : QgModeData ι)

theorem BookProof.QgTruncationResolvent.starobinsky_qgContinuum_momentumCutoff_flow_convergence (M alpha : ℝ)
    (halpha : 0 < alpha) (g : ℝ) :
    ∃ (T : UnboundedSelfAdjoint (Sec CMode)) (S : ℕ → UnboundedSelfAdjoint (Sec CMode)),
      IsSelfAdjointExtension
          (secHam (starobinskyWall M alpha halpha) (qgContinuumModes g)) T.op ∧
        (∀ n, IsSelfAdjointExtension (secHam (starobinskyWall M alpha halpha)
          (truncModes (qgContinuumModes g) (momWindow n))) (S n).op) ∧
        StrongResolventConvergence T S ∧
        ∀ (v : Sec CMode) (T₀ : ℝ), 0 ≤ T₀ →
          TendstoUniformlyOn (fun n t => (S n).stoneU t v) (fun t => T.stoneU t v) atTop
              (Set.Icc (-T₀) T₀) ∧
            ∀ t : ℝ, Tendsto (fun n => (S n).stoneU t v) atTop (𝓝 (T.stoneU t v)) := by sorry
