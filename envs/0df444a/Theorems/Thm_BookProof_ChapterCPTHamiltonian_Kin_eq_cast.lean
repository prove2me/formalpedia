-- Prove2me | Theorems.Thm_BookProof_ChapterCPTHamiltonian_Kin_eq_cast
-- name    : BookProof.ChapterCPTHamiltonian.Kin_eq_cast
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:22:26.637647+00:00
-- url     : https://prove2.me/theorems/2accf340-2a00-462e-b07b-87e8de1d9453
-- title:
--   `BookProof.ChapterCPTHamiltonian.Kin_eq_cast` (j : Fin 3) : Kin j = (Int.castRingHom ℂ).mapMatrix (KinZ j)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCPTHamiltonian`.
--
--   `BookProof.ChapterCPTHamiltonian.Kin_eq_cast` (j : Fin 3) : Kin j = (Int.castRingHom ℂ).mapMatrix (KinZ j)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCPTHamiltonian.Kin_eq_cast`.

-- Generated from ChapterCPTHamiltonian.lean — theorem BookProof.ChapterCPTHamiltonian.Kin_eq_cast
import Mathlib
import Definitions.Def_ChapterCPTHamiltonian
import Definitions.Def_ChapterA3
open BookProof.ChapterA3
open BookProof.ChapterCPTHamiltonian


open Matrix


open BookProof.ChapterA3

theorem BookProof.ChapterCPTHamiltonian.Kin_eq_cast (j : Fin 3) :
    Kin j = (Int.castRingHom ℂ).mapMatrix (KinZ j) := by sorry
