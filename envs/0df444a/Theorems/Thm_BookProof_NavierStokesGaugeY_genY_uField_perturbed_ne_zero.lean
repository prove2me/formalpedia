-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY_genY_uField_perturbed_ne_zero
-- name    : BookProof.NavierStokesGaugeY.genY_uField_perturbed_ne_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T17:42:58.354985+00:00
-- url     : https://prove2.me/theorems/fa8664fc-0299-4945-8a86-20269e8ecb5b
-- title:
--   `BookProof.NavierStokesGaugeY.genY_uField_perturbed_ne_zero` (i j : Fin 3) (c : ℂ) (hc : c ≠ 0) : genY j (uField i + C c * X (NSVar.y j)) ≠ 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY`.
--
--   `BookProof.NavierStokesGaugeY.genY_uField_perturbed_ne_zero` (i j : Fin 3) (c : ℂ) (hc : c ≠ 0) : genY j (uField i + C c * X (NSVar.y j)) ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY.genY_uField_perturbed_ne_zero`.

-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.genY_uField_perturbed_ne_zero
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow

theorem BookProof.NavierStokesGaugeY.genY_uField_perturbed_ne_zero (i j : Fin 3) (c : ℂ) (hc : c ≠ 0) :
    genY j (uField i + C c * X (NSVar.y j)) ≠ 0 := by sorry
