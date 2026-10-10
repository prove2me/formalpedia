-- Prove2me | Theorems.Thm_BookProof_NavierStokesEulerian_derivativeField_second
-- name    : BookProof.NavierStokesEulerian.derivativeField_second
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:41:36.105168+00:00
-- url     : https://prove2.me/theorems/ee1f0697-9059-4919-a4d1-a7d4f7427cb7
-- title:
--   `BookProof.NavierStokesEulerian.derivativeField_second` (uD : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℝ) (uDD : Fin 3 → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℝ) (M : Fin 3 → Fin 3 →...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesEulerian`.
--
--   `BookProof.NavierStokesEulerian.derivativeField_second` (uD : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℝ) (uDD : Fin 3 → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℝ) (M : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ((Fin 3 → ℝ) →L[ℝ] ℝ)) (huD : ∀ i j x, HasFDerivAt (uD i j) (M i j x) x) (huDD : ∀ i j k x, uDD i j k x = M i j x (evec k)) (i j k : Fin 3) (x : Fin 3 → ℝ) : uDD i j k x = dirDeriv (uD i j) k x
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesEulerian.derivativeField_second`.

-- Generated from ChapterNavierStokesEulerian.lean — theorem BookProof.NavierStokesEulerian.derivativeField_second
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesEulerian
open BookProof.NavierStokesEulerian



open BookProof.NavierStokesFlow Matrix

theorem BookProof.NavierStokesEulerian.derivativeField_second (uD : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℝ)
    (uDD : Fin 3 → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℝ)
    (M : Fin 3 → Fin 3 → (Fin 3 → ℝ) → ((Fin 3 → ℝ) →L[ℝ] ℝ))
    (huD : ∀ i j x, HasFDerivAt (uD i j) (M i j x) x)
    (huDD : ∀ i j k x, uDD i j k x = M i j x (evec k)) (i j k : Fin 3) (x : Fin 3 → ℝ) :
    uDD i j k x = dirDeriv (uD i j) k x := by sorry
