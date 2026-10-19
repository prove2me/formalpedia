-- Prove2me | Theorems.Thm_BookProof_ChapterA_Rpseudoreal_realCommutant_eq_quaternion
-- name    : BookProof.ChapterA.Rpseudoreal_realCommutant_eq_quaternion
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:18:51.692528+00:00
-- url     : https://prove2.me/theorems/ce329795-616a-42c4-8e96-7c60a9b2df0f
-- title:
--   `BookProof.ChapterA.Rpseudoreal_realCommutant_eq_quaternion` (M : System ℂ V) (hSchur : IsSchurFull M) {θ : AntiUnitary V} (hθ : ∀ x, θ (θ x) = -x) (hθc : CommutesAntiUnitary M θ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA2c`.
--
--   `BookProof.ChapterA.Rpseudoreal_realCommutant_eq_quaternion` (M : System ℂ V) (hSchur : IsSchurFull M) {θ : AntiUnitary V} (hθ : ∀ x, θ (θ x) = -x) (hθc : CommutesAntiUnitary M θ) (S : V →L[ℝ] V) : RealCommutes M S ↔ ∃ q : Quaternion ℝ, S = qembed θ hθ q
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.Rpseudoreal_realCommutant_eq_quaternion`.

-- Generated from ChapterA2c.lean — theorem BookProof.ChapterA.Rpseudoreal_realCommutant_eq_quaternion
import Mathlib
import Definitions.Def_ChapterA2c
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterA.Rpseudoreal_realCommutant_eq_quaternion (M : System ℂ V) (hSchur : IsSchurFull M)
    {θ : AntiUnitary V} (hθ : ∀ x, θ (θ x) = -x) (hθc : CommutesAntiUnitary M θ)
    (S : V →L[ℝ] V) :
    RealCommutes M S ↔ ∃ q : Quaternion ℝ, S = qembed θ hθ q := by sorry
