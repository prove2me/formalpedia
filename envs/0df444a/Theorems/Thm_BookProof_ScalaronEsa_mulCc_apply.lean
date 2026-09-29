-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_mulCc_apply
-- name    : BookProof.ScalaronEsa.mulCc_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T13:42:36.32851+00:00
-- url     : https://prove2.me/theorems/e91d6c68-a26c-4033-926e-a5939dc6a57c
-- title:
--   The Lean 4 theorem `mulCc_apply` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mulCc_apply` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.mulCc_apply
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

theorem BookProof.ScalaronEsa.mulCc_apply (W : E → ℝ) (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (f : ccSchwartz E) (x : E) :
    (mulCc W hW f) x = (W x : ℂ) * (f : 𝓢(E, ℂ)) x := by sorry
