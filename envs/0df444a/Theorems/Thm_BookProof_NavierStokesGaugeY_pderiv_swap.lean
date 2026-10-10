-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY_pderiv_swap
-- name    : BookProof.NavierStokesGaugeY.pderiv_swap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:24:08.334781+00:00
-- url     : https://prove2.me/theorems/d246fe3d-7b9a-48ed-973f-cbd0ff3177d2
-- title:
--   `BookProof.NavierStokesGaugeY.pderiv_swap` (a b : NSVar) (p : NSAlg) : pderiv a (pderiv b p) = pderiv b (pderiv a p)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY`.
--
--   `BookProof.NavierStokesGaugeY.pderiv_swap` (a b : NSVar) (p : NSAlg) : pderiv a (pderiv b p) = pderiv b (pderiv a p)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY.pderiv_swap`.

-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.pderiv_swap
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow

theorem BookProof.NavierStokesGaugeY.pderiv_swap (a b : NSVar) (p : NSAlg) :
    pderiv a (pderiv b p) = pderiv b (pderiv a p) := by sorry
