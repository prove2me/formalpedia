-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY_hamiltonianOp_apply_of_y_zero
-- name    : BookProof.NavierStokesGaugeY.hamiltonianOp_apply_of_y_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:24:54.638565+00:00
-- url     : https://prove2.me/theorems/f35f813c-3e66-4840-a15e-7c34e6ca825d
-- title:
--   `BookProof.NavierStokesGaugeY.hamiltonianOp_apply_of_y_zero` (nu : ℂ) (mom : Fin 3 → E →ₗ[ℂ] E) (u : Fin 3 → E →ₗ[ℂ] E) (uD : Fin 3 → Fin 3 → E →ₗ[ℂ] E) (uL : Fin 3...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY`.
--
--   `BookProof.NavierStokesGaugeY.hamiltonianOp_apply_of_y_zero` (nu : ℂ) (mom : Fin 3 → E →ₗ[ℂ] E) (u : Fin 3 → E →ₗ[ℂ] E) (uD : Fin 3 → Fin 3 → E →ₗ[ℂ] E) (uL : Fin 3 → E →ₗ[ℂ] E) (Y : Fin 3 → E →ₗ[ℂ] E) (hcomm : ∀ i j k, Y k ∘ₗ uD i j = uD i j ∘ₗ Y k) (hmom : ∀ i k, Y k ∘ₗ mom i = mom i ∘ₗ Y k) (v : E) (hv : ∀ j, Y j v = 0) : hamiltonianOp nu mom u uD uL Y v = hamiltonianPoint nu mom u uD uL v
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY.hamiltonianOp_apply_of_y_zero`.

-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.hamiltonianOp_apply_of_y_zero
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

theorem BookProof.NavierStokesGaugeY.hamiltonianOp_apply_of_y_zero (nu : ℂ) (mom : Fin 3 → E →ₗ[ℂ] E)
    (u : Fin 3 → E →ₗ[ℂ] E) (uD : Fin 3 → Fin 3 → E →ₗ[ℂ] E) (uL : Fin 3 → E →ₗ[ℂ] E)
    (Y : Fin 3 → E →ₗ[ℂ] E) (hcomm : ∀ i j k, Y k ∘ₗ uD i j = uD i j ∘ₗ Y k)
    (hmom : ∀ i k, Y k ∘ₗ mom i = mom i ∘ₗ Y k) (v : E) (hv : ∀ j, Y j v = 0) :
    hamiltonianOp nu mom u uD uL Y v = hamiltonianPoint nu mom u uD uL v := by sorry
