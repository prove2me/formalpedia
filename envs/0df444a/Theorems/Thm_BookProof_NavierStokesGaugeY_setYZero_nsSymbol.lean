-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY_setYZero_nsSymbol
-- name    : BookProof.NavierStokesGaugeY.setYZero_nsSymbol
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:19:20.977171+00:00
-- url     : https://prove2.me/theorems/9e94cb05-3a29-48fb-9059-df1c8698f8c0
-- title:
--   `BookProof.NavierStokesGaugeY.setYZero_nsSymbol` (nu : ℂ) (i : Fin 3) : setYZero (nsSymbol nu i) = nsSymbolPoint nu i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY`.
--
--   `BookProof.NavierStokesGaugeY.setYZero_nsSymbol` (nu : ℂ) (i : Fin 3) : setYZero (nsSymbol nu i) = nsSymbolPoint nu i
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY.setYZero_nsSymbol`.

-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.setYZero_nsSymbol
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow

theorem BookProof.NavierStokesGaugeY.setYZero_nsSymbol (nu : ℂ) (i : Fin 3) :
    setYZero (nsSymbol nu i) = nsSymbolPoint nu i := by sorry
