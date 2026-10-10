-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY_genY_genY_expand
-- name    : BookProof.NavierStokesGaugeY.genY_genY_expand
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T17:43:10.444742+00:00
-- url     : https://prove2.me/theorems/0f6161cf-e918-4c82-aa19-c5ce08952452
-- title:
--   `BookProof.NavierStokesGaugeY.genY_genY_expand` (j k : Fin 3) (p : NSAlg) : genY j (genY k p) = pderiv (NSVar.y j) (pderiv (NSVar.y k) p) - ∑ i : Fin 3, X (NSVar.uD i j) * pderiv (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY`.
--
--   `BookProof.NavierStokesGaugeY.genY_genY_expand` (j k : Fin 3) (p : NSAlg) : genY j (genY k p) = pderiv (NSVar.y j) (pderiv (NSVar.y k) p) - ∑ i : Fin 3, X (NSVar.uD i j) * pderiv (NSVar.y k) (pderiv (NSVar.u i) p) - ∑ i : Fin 3, X (NSVar.uD i k) * pderiv (NSVar.y j) (pderiv (NSVar.u i) p) + ∑ i : Fin 3, ∑ m : Fin 3, X (NSVar.uD i j) * X (NSVar.uD m k) * pderiv (NSVar.u i) (pderiv (NSVar.u m) p)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY.genY_genY_expand`.

-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.genY_genY_expand
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow

theorem BookProof.NavierStokesGaugeY.genY_genY_expand (j k : Fin 3) (p : NSAlg) :
    genY j (genY k p) =
      pderiv (NSVar.y j) (pderiv (NSVar.y k) p)
      - ∑ i : Fin 3, X (NSVar.uD i j) * pderiv (NSVar.y k) (pderiv (NSVar.u i) p)
      - ∑ i : Fin 3, X (NSVar.uD i k) * pderiv (NSVar.y j) (pderiv (NSVar.u i) p)
      + ∑ i : Fin 3, ∑ m : Fin 3,
          X (NSVar.uD i j) * X (NSVar.uD m k) * pderiv (NSVar.u i) (pderiv (NSVar.u m) p) := by sorry
