-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY_genY_uField_perturbed
-- name    : BookProof.NavierStokesGaugeY.genY_uField_perturbed
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T17:42:52.164129+00:00
-- url     : https://prove2.me/theorems/6f84fdc3-cf81-4280-93fb-239c1a23257c
-- title:
--   `BookProof.NavierStokesGaugeY.genY_uField_perturbed` (i j : Fin 3) (c : ℂ) : genY j (uField i + C c * X (NSVar.y j)) = C c
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY`.
--
--   `BookProof.NavierStokesGaugeY.genY_uField_perturbed` (i j : Fin 3) (c : ℂ) : genY j (uField i + C c * X (NSVar.y j)) = C c
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY.genY_uField_perturbed`.

-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.genY_uField_perturbed
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow

theorem BookProof.NavierStokesGaugeY.genY_uField_perturbed (i j : Fin 3) (c : ℂ) :
    genY j (uField i + C c * X (NSVar.y j)) = C c := by sorry
