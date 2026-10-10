-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY_advectionOp_apply_of_y_zero
-- name    : BookProof.NavierStokesGaugeY.advectionOp_apply_of_y_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:24:49.914103+00:00
-- url     : https://prove2.me/theorems/39dd1a6f-ca32-4541-9500-44902f8c6dff
-- title:
--   `BookProof.NavierStokesGaugeY.advectionOp_apply_of_y_zero` (nu : ℂ) (u : Fin 3 → E →ₗ[ℂ] E) (uD : Fin 3 → Fin 3 → E →ₗ[ℂ] E) (uL : Fin 3 → E →ₗ[ℂ] E) (Y : Fin 3 →...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY`.
--
--   `BookProof.NavierStokesGaugeY.advectionOp_apply_of_y_zero` (nu : ℂ) (u : Fin 3 → E →ₗ[ℂ] E) (uD : Fin 3 → Fin 3 → E →ₗ[ℂ] E) (uL : Fin 3 → E →ₗ[ℂ] E) (Y : Fin 3 → E →ₗ[ℂ] E) (hcomm : ∀ i j k, Y k ∘ₗ uD i j = uD i j ∘ₗ Y k) (v : E) (hv : ∀ j, Y j v = 0) (i : Fin 3) : advectionOp nu u uD uL Y i v = advectionPoint nu u uD uL i v
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY.advectionOp_apply_of_y_zero`.

-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.advectionOp_apply_of_y_zero
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

theorem BookProof.NavierStokesGaugeY.advectionOp_apply_of_y_zero (nu : ℂ) (u : Fin 3 → E →ₗ[ℂ] E)
    (uD : Fin 3 → Fin 3 → E →ₗ[ℂ] E) (uL : Fin 3 → E →ₗ[ℂ] E) (Y : Fin 3 → E →ₗ[ℂ] E)
    (hcomm : ∀ i j k, Y k ∘ₗ uD i j = uD i j ∘ₗ Y k) (v : E) (hv : ∀ j, Y j v = 0)
    (i : Fin 3) :
    advectionOp nu u uD uL Y i v = advectionPoint nu u uD uL i v := by sorry
