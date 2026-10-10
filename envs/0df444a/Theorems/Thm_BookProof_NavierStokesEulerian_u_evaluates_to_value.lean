-- Prove2me | Theorems.Thm_BookProof_NavierStokesEulerian_u_evaluates_to_value
-- name    : BookProof.NavierStokesEulerian.u_evaluates_to_value
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:38:53.977985+00:00
-- url     : https://prove2.me/theorems/2071ff4f-bd0b-4a24-8b6d-9f444be3c4b1
-- title:
--   `BookProof.NavierStokesEulerian.u_evaluates_to_value` {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*} [Fintype ι] (u : Fin 3 → E →ₗ[ℂ] E) (uD : Fin 3 → ι → E →ₗ[ℂ] E)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesEulerian`.
--
--   `BookProof.NavierStokesEulerian.u_evaluates_to_value` {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*} [Fintype ι] (u : Fin 3 → E →ₗ[ℂ] E) (uD : Fin 3 → ι → E →ₗ[ℂ] E) (X : ι → E →ₗ[ℂ] E) (x : ι → ℂ) (v : E) (hv : ∀ i, X i v = x i • v) (i : Fin 3) : fieldTaylor (u i) (uD i) X x v = u i v
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesEulerian.u_evaluates_to_value`.

-- Generated from ChapterNavierStokesEulerian.lean — theorem BookProof.NavierStokesEulerian.u_evaluates_to_value
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesEulerian
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesEulerian



open BookProof.NavierStokesFlow Matrix

theorem BookProof.NavierStokesEulerian.u_evaluates_to_value {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*} [Fintype ι]
    (u : Fin 3 → E →ₗ[ℂ] E) (uD : Fin 3 → ι → E →ₗ[ℂ] E) (X : ι → E →ₗ[ℂ] E) (x : ι → ℂ)
    (v : E) (hv : ∀ i, X i v = x i • v) (i : Fin 3) :
    fieldTaylor (u i) (uD i) X x v = u i v := by sorry
