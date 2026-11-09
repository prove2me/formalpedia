-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFlow_qgOuterFock_numerical_flow_convergence
-- name    : BookProof.QgOuterFockFlow.qgOuterFock_numerical_flow_convergence
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T10:18:30.923445+00:00
-- url     : https://prove2.me/theorems/5d33c591-45b5-4f80-95d0-03f3688641b8
-- title:
--   The Lean 4 theorem `qgOuterFock_numerical_flow_convergence` in the `ChapterQgOuterFockFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgOuterFock_numerical_flow_convergence` in the `ChapterQgOuterFockFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockFlow.lean

-- Generated from ChapterQgOuterFockFlow.lean — theorem BookProof.QgOuterFockFlow.qgOuterFock_numerical_flow_convergence
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterQgContinuumModeInstance
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Mathlib
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
open BookProof.EsaClosure
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData
open BookProof.ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent
open BookProof.StoneBridge
open Filter Topology
open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgContinuumModeInstance
open BookProof.FarisLavine BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.StoneBridge BookProof.ChapterStoneResolvent BookProof.EsaClosure
open BookProof.ChapterSirkTrotterKato

noncomputable section

variable {ι : Type*} (W : WallPot) (Q : QgModeData ι)

theorem BookProof.QgOuterFockFlow.qgOuterFock_numerical_flow_convergence :
    ∃ (T : UnboundedSelfAdjoint (Sec ι)) (U : ℝ → (Sec ι →L[ℂ] Sec ι)),
      IsSelfAdjointExtension (secData W Q).ext T.op ∧ IsStoneFlow T U ∧
        ∀ S : ℕ → UnboundedSelfAdjoint (Sec ι), StrongResolventConvergence T S →
          ∀ (v : Sec ι) (T₀ : ℝ), 0 ≤ T₀ →
            (TendstoUniformlyOn (fun n t => (S n).stoneU t v) (fun t => T.stoneU t v) atTop
                (Set.Icc (-T₀) T₀)
              ∧ ∀ t : ℝ, Tendsto (fun n => (S n).stoneU t v) atTop (𝓝 (T.stoneU t v))) := by sorry
