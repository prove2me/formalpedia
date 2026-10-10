-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY_uFieldOp_apply_of_y_zero
-- name    : BookProof.NavierStokesGaugeY.uFieldOp_apply_of_y_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:24:40.330979+00:00
-- url     : https://prove2.me/theorems/0ec0a1f8-9af5-4e10-8ee4-d4a3b578fc0f
-- title:
--   `BookProof.NavierStokesGaugeY.uFieldOp_apply_of_y_zero` (u : Fin 3 → E →ₗ[ℂ] E) (uD : Fin 3 → Fin 3 → E →ₗ[ℂ] E) (Y : Fin 3 → E →ₗ[ℂ] E) (v : E) (hv : ∀ j, Y j v = 0)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY`.
--
--   `BookProof.NavierStokesGaugeY.uFieldOp_apply_of_y_zero` (u : Fin 3 → E →ₗ[ℂ] E) (uD : Fin 3 → Fin 3 → E →ₗ[ℂ] E) (Y : Fin 3 → E →ₗ[ℂ] E) (v : E) (hv : ∀ j, Y j v = 0) (i : Fin 3) : uFieldOp u uD Y i v = u i v
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY.uFieldOp_apply_of_y_zero`.

-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.uFieldOp_apply_of_y_zero
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

theorem BookProof.NavierStokesGaugeY.uFieldOp_apply_of_y_zero (u : Fin 3 → E →ₗ[ℂ] E) (uD : Fin 3 → Fin 3 → E →ₗ[ℂ] E)
    (Y : Fin 3 → E →ₗ[ℂ] E) (v : E) (hv : ∀ j, Y j v = 0) (i : Fin 3) :
    uFieldOp u uD Y i v = u i v := by sorry
