-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_opCc_apply
-- name    : BookProof.ScalaronEsa.opCc_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T13:42:33.160986+00:00
-- url     : https://prove2.me/theorems/efe9d79d-bca9-49fc-a0df-fce7cb660d34
-- title:
--   The Lean 4 theorem `opCc_apply` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `opCc_apply` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.opCc_apply
import Mathlib
import Definitions.Def_ChapterScalaronCoreEsa
open BookProof.ScalaronEsa


open Filter Topology MeasureTheory SchwartzMap


open BookProof.StrichartzWave BookProof.FarisLavine BookProof.Starobinsky
open BookProof.QuantumGravityDensitized BookProof.StoneBridge BookProof.NavierStokesFlow
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem BookProof.ScalaronEsa.opCc_apply (W : E → ℝ) (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (f : ccSchwartz E) :
    opCc W hW (ccEquiv E f) = (mulCc W hW f).toLp 2 (volume : Measure E) := by sorry
