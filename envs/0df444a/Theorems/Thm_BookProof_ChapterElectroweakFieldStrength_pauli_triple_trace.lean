-- Prove2me | Theorems.Thm_BookProof_ChapterElectroweakFieldStrength_pauli_triple_trace
-- name    : BookProof.ChapterElectroweakFieldStrength.pauli_triple_trace
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T02:43:00.754561+00:00
-- url     : https://prove2.me/theorems/1b6dba37-5c02-44ea-9b3b-b660a669a6ed
-- title:
--   `BookProof.ChapterElectroweakFieldStrength.pauli_triple_trace` (a b c : Fin 3) : (pauliV a * pauliV b * pauliV c).trace = 2 * Complex.I * eps a b c
-- statement:
--   Prove the following Lean 4 theorem from `ChapterElectroweakFieldStrength`.
--
--   `BookProof.ChapterElectroweakFieldStrength.pauli_triple_trace` (a b c : Fin 3) : (pauliV a * pauliV b * pauliV c).trace = 2 * Complex.I * eps a b c
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterElectroweakFieldStrength.pauli_triple_trace`.

-- Generated from ChapterElectroweakFieldStrength.lean — theorem BookProof.ChapterElectroweakFieldStrength.pauli_triple_trace
import Definitions.Def_ChapterParity
import Mathlib
import Definitions.Def_ChapterElectroweakFieldStrength
import Definitions.Def_ChapterParitySU2
open BookProof.ChapterParitySU2
open BookProof.ChapterElectroweakFieldStrength


open Matrix


open BookProof.ChapterParity BookProof.ChapterParitySU2

theorem BookProof.ChapterElectroweakFieldStrength.pauli_triple_trace (a b c : Fin 3) :
    (pauliV a * pauliV b * pauliV c).trace = 2 * Complex.I * eps a b c := by sorry
