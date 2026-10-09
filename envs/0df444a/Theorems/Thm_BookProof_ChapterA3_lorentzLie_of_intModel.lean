-- Prove2me | Theorems.Thm_BookProof_ChapterA3_lorentzLie_of_intModel
-- name    : BookProof.ChapterA3.lorentzLie_of_intModel
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:43:43.696982+00:00
-- url     : https://prove2.me/theorems/38b053c7-5b44-4b79-906b-9db81bd9ea8a
-- title:
--   `BookProof.ChapterA3.lorentzLie_of_intModel` (Az : Matrix (Fin 4) (Fin 4) ℤ) (h : Az * minkowskiMatZ + minkowskiMatZ * Azᵀ = 0) : (Int.castRingHom ℝ).mapMatrix Az ∈ LorentzLie
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3e`.
--
--   `BookProof.ChapterA3.lorentzLie_of_intModel` (Az : Matrix (Fin 4) (Fin 4) ℤ) (h : Az * minkowskiMatZ + minkowskiMatZ * Azᵀ = 0) : (Int.castRingHom ℝ).mapMatrix Az ∈ LorentzLie
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.lorentzLie_of_intModel`.

-- Generated from ChapterA3e.lean — theorem BookProof.ChapterA3.lorentzLie_of_intModel
import Mathlib
import Definitions.Def_ChapterA3e
import Definitions.Def_ChapterA3b
import Definitions.Def_ChapterA3d
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix

theorem BookProof.ChapterA3.lorentzLie_of_intModel (Az : Matrix (Fin 4) (Fin 4) ℤ)
    (h : Az * minkowskiMatZ + minkowskiMatZ * Azᵀ = 0) :
    (Int.castRingHom ℝ).mapMatrix Az ∈ LorentzLie := by sorry
