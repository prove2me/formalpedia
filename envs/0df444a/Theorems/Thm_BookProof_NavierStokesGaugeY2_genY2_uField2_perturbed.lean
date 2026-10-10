-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY2_genY2_uField2_perturbed
-- name    : BookProof.NavierStokesGaugeY2.genY2_uField2_perturbed
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T17:44:27.972195+00:00
-- url     : https://prove2.me/theorems/562500cb-1a05-4fe9-9231-27adbd5a772e
-- title:
--   `BookProof.NavierStokesGaugeY2.genY2_uField2_perturbed` (i j : Fin 3) (c : ℂ) : genY2 j (uField2 i + C c * (X (NSVar.y j) * X (NSVar.y j))) = C c * (2 * X (NSVar.y j))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY2`.
--
--   `BookProof.NavierStokesGaugeY2.genY2_uField2_perturbed` (i j : Fin 3) (c : ℂ) : genY2 j (uField2 i + C c * (X (NSVar.y j) * X (NSVar.y j))) = C c * (2 * X (NSVar.y j))
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY2.genY2_uField2_perturbed`.

-- Generated from ChapterNavierStokesGaugeY2.lean — theorem BookProof.NavierStokesGaugeY2.genY2_uField2_perturbed
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesGaugeY2



open MvPolynomial BookProof.NavierStokesGaugeY

theorem BookProof.NavierStokesGaugeY2.genY2_uField2_perturbed (i j : Fin 3) (c : ℂ) :
    genY2 j (uField2 i + C c * (X (NSVar.y j) * X (NSVar.y j)))
      = C c * (2 * X (NSVar.y j)) := by sorry
