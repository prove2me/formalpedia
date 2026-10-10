-- Prove2me | Theorems.Thm_BookProof_NavierStokesEulerian_derivativeField_relates_to_field
-- name    : BookProof.NavierStokesEulerian.derivativeField_relates_to_field
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:40:13.812257+00:00
-- url     : https://prove2.me/theorems/8819d55d-0630-4b10-b785-6a108ecc1811
-- title:
--   `BookProof.NavierStokesEulerian.derivativeField_relates_to_field` (u : (Fin 3 → ℝ) → Fin 3 → ℝ) (uD : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℝ) (L : Fin 3 → (Fin 3 → ℝ) →...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesEulerian`.
--
--   `BookProof.NavierStokesEulerian.derivativeField_relates_to_field` (u : (Fin 3 → ℝ) → Fin 3 → ℝ) (uD : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℝ) (L : Fin 3 → (Fin 3 → ℝ) → ((Fin 3 → ℝ) →L[ℝ] ℝ)) (hu : ∀ i x, HasFDerivAt (fun y => u y i) (L i x) x) (huD : ∀ i j x, uD i j x = L i x (evec j)) (i j : Fin 3) (x : Fin 3 → ℝ) : uD i j x = dirDeriv (fun y => u y i) j x
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesEulerian.derivativeField_relates_to_field`.

-- Generated from ChapterNavierStokesEulerian.lean — theorem BookProof.NavierStokesEulerian.derivativeField_relates_to_field
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesEulerian
open BookProof.NavierStokesEulerian



open BookProof.NavierStokesFlow Matrix

theorem BookProof.NavierStokesEulerian.derivativeField_relates_to_field (u : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (uD : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℝ) (L : Fin 3 → (Fin 3 → ℝ) → ((Fin 3 → ℝ) →L[ℝ] ℝ))
    (hu : ∀ i x, HasFDerivAt (fun y => u y i) (L i x) x)
    (huD : ∀ i j x, uD i j x = L i x (evec j)) (i j : Fin 3) (x : Fin 3 → ℝ) :
    uD i j x = dirDeriv (fun y => u y i) j x := by sorry
