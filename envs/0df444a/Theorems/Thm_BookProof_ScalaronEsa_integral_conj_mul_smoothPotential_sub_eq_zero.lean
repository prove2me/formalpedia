-- Prove2me | Theorems.Thm_BookProof_ScalaronEsa_integral_conj_mul_smoothPotential_sub_eq_zero
-- name    : BookProof.ScalaronEsa.integral_conj_mul_smoothPotential_sub_eq_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:21:31.794047+00:00
-- url     : https://prove2.me/theorems/f6b0fb1a-9251-4539-841f-4f9470182f17
-- title:
--   The Lean 4 theorem `integral_conj_mul_smoothPotential_sub_eq_zero` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `integral_conj_mul_smoothPotential_sub_eq_zero` in the `ChapterScalaronCoreEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronCoreEsa.lean

-- Generated from ChapterScalaronCoreEsa.lean — theorem BookProof.ScalaronEsa.integral_conj_mul_smoothPotential_sub_eq_zero
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

theorem BookProof.ScalaronEsa.integral_conj_mul_smoothPotential_sub_eq_zero (W : E → ℝ)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (z : ℂ)
    (u : Lp ℂ 2 (volume : Measure E))
    (hu : ∀ v : ccDomain E,
      (inner ℂ (opCc W hW v) u : ℂ) = z * inner ℂ (v : Lp ℂ 2 _) u)
    (ψ : ccSchwartz E) :
    ∫ x, (starRingEnd ℂ) ((ψ : 𝓢(E, ℂ)) x) * (((W x : ℝ) : ℂ) - z) * (u x) = 0 := by sorry
