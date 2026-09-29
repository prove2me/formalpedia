-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_starobinskyV_essentiallySelfAdjoint
-- name    : BookProof.ScalaronEsa.starobinskyV_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:20:18.919437+00:00
-- url     : https://prove2.me/theorems/a4fb94d6-8fa5-4fa6-ad78-1522aa9bdccc
-- title:
--   The Lean 4 theorem `starobinskyV_essentiallySelfAdjoint` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `starobinskyV_essentiallySelfAdjoint` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.starobinskyV_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterScalaronCoreEsa
import Theorems.Thm_BookProof_ScalaronEsa_contDiff_starobinskyV
open BookProof.ScalaronEsa


open Filter Topology MeasureTheory SchwartzMap


open BookProof.StrichartzWave BookProof.FarisLavine BookProof.Starobinsky
open BookProof.QuantumGravityDensitized BookProof.StoneBridge BookProof.NavierStokesFlow
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem BookProof.ScalaronEsa.starobinskyV_essentiallySelfAdjoint (M alpha : ℝ) :
    EssentiallySelfAdjointOn (ccDomain ℝ)
      (opCc (fun phi : ℝ => starobinskyV M alpha phi) (contDiff_starobinskyV M alpha)) := by sorry
