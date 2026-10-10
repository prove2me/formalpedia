-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY_y_zero_of_commute
-- name    : BookProof.NavierStokesGaugeY.y_zero_of_commute
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:25:26.606974+00:00
-- url     : https://prove2.me/theorems/37d1c556-cd81-42f5-bb05-c984f95b0bb5
-- title:
--   `BookProof.NavierStokesGaugeY.y_zero_of_commute` (Y : Fin 3 → E →ₗ[ℂ] E) (T : E →ₗ[ℂ] E) (hT : ∀ j, Y j ∘ₗ T = T ∘ₗ Y j) (v : E) (hv : ∀ j, Y j v = 0) (j : Fin 3) : Y j...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY`.
--
--   `BookProof.NavierStokesGaugeY.y_zero_of_commute` (Y : Fin 3 → E →ₗ[ℂ] E) (T : E →ₗ[ℂ] E) (hT : ∀ j, Y j ∘ₗ T = T ∘ₗ Y j) (v : E) (hv : ∀ j, Y j v = 0) (j : Fin 3) : Y j (T v) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY.y_zero_of_commute`.

-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.y_zero_of_commute
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

theorem BookProof.NavierStokesGaugeY.y_zero_of_commute (Y : Fin 3 → E →ₗ[ℂ] E) (T : E →ₗ[ℂ] E)
    (hT : ∀ j, Y j ∘ₗ T = T ∘ₗ Y j) (v : E) (hv : ∀ j, Y j v = 0) (j : Fin 3) :
    Y j (T v) = 0 := by sorry
