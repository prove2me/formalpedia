-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_qgScalaron_stone_flow
-- name    : BookProof.ScalaronEsa.qgScalaron_stone_flow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:33:36.624146+00:00
-- url     : https://prove2.me/theorems/f9c94f14-7440-4c04-9d43-5d19c2a4842d
-- title:
--   The Lean 4 theorem `qgScalaron_stone_flow` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgScalaron_stone_flow` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.qgScalaron_stone_flow
import Mathlib
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterMajoranaClifford
import Definitions.Def_ChapterMajoranaClifford
open BookProof.MajoranaClifford
open BookProof.ScalaronEsa


open Filter Topology MeasureTheory SchwartzMap


open BookProof.StrichartzWave BookProof.FarisLavine BookProof.Starobinsky
open BookProof.QuantumGravityDensitized BookProof.StoneBridge BookProof.NavierStokesFlow
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable (a b : ℕ → ℝ) (M alpha : ℝ) (Rc phi : ℕ → ℝ)

theorem BookProof.ScalaronEsa.qgScalaron_stone_flow :
    ∃ (T : UnboundedSelfAdjoint L2Nat) (U : ℝ → (L2Nat →L[ℂ] L2Nat)),
      IsSelfAdjointExtension (qgScalaronModeHamiltonian a b M alpha Rc phi) T.op ∧
        IsStoneFlow T U := by sorry
