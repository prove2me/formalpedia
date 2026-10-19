-- Prove2me | Theorems.Thm_BookProof_FriedrichsSquare_adjPairs_mono
-- name    : BookProof.FriedrichsSquare.adjPairs_mono
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:40:07.043699+00:00
-- url     : https://prove2.me/theorems/8084696a-1396-438f-a669-cbc530566d96
-- title:
--   `BookProof.FriedrichsSquare.adjPairs_mono` {G H : Submodule ℂ (F × F)} (h : G ≤ H) : adjPairs H ≤ adjPairs G
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsSquareFactorization`.
--
--   `BookProof.FriedrichsSquare.adjPairs_mono` {G H : Submodule ℂ (F × F)} (h : G ≤ H) : adjPairs H ≤ adjPairs G
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsSquare.adjPairs_mono`.

-- Generated from ChapterFriedrichsSquareFactorization.lean — theorem BookProof.FriedrichsSquare.adjPairs_mono
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Definitions.Def_ChapterClosureUniqueness
open BookProof.ClosureUniqueness
open BookProof.FriedrichsSquare



open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

theorem BookProof.FriedrichsSquare.adjPairs_mono {G H : Submodule ℂ (F × F)} (h : G ≤ H) : adjPairs H ≤ adjPairs G := by sorry
