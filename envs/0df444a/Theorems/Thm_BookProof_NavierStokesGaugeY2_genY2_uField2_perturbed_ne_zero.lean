-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY2_genY2_uField2_perturbed_ne_zero
-- name    : BookProof.NavierStokesGaugeY2.genY2_uField2_perturbed_ne_zero
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T17:44:34.571435+00:00
-- url     : https://prove2.me/theorems/302f5617-4e22-4bcb-acb6-7e8d7998ffeb
-- title:
--   `BookProof.NavierStokesGaugeY2.genY2_uField2_perturbed_ne_zero` (i j : Fin 3) (c : ℂ) (hc : c ≠ 0) : genY2 j (uField2 i + C c * (X (NSVar.y j) * X (NSVar.y j))) ≠ 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY2`.
--
--   `BookProof.NavierStokesGaugeY2.genY2_uField2_perturbed_ne_zero` (i j : Fin 3) (c : ℂ) (hc : c ≠ 0) : genY2 j (uField2 i + C c * (X (NSVar.y j) * X (NSVar.y j))) ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY2.genY2_uField2_perturbed_ne_zero`.

-- Generated from ChapterNavierStokesGaugeY2.lean — theorem BookProof.NavierStokesGaugeY2.genY2_uField2_perturbed_ne_zero
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesGaugeY2



open MvPolynomial BookProof.NavierStokesGaugeY

theorem BookProof.NavierStokesGaugeY2.genY2_uField2_perturbed_ne_zero (i j : Fin 3) (c : ℂ) (hc : c ≠ 0) :
    genY2 j (uField2 i + C c * (X (NSVar.y j) * X (NSVar.y j))) ≠ 0 := by sorry
