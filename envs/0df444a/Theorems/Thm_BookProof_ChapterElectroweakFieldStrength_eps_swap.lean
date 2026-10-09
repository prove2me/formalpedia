-- Prove2me | Theorems.Thm_BookProof_ChapterElectroweakFieldStrength_eps_swap
-- name    : BookProof.ChapterElectroweakFieldStrength.eps_swap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T23:15:15.230416+00:00
-- url     : https://prove2.me/theorems/06b04b03-4d27-4469-872f-8e71b2747000
-- title:
--   `BookProof.ChapterElectroweakFieldStrength.eps_swap` (a b c : Fin 3) : eps a b c = -eps b a c
-- statement:
--   Prove the following Lean 4 theorem from `ChapterElectroweakFieldStrength`.
--
--   `BookProof.ChapterElectroweakFieldStrength.eps_swap` (a b c : Fin 3) : eps a b c = -eps b a c
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterElectroweakFieldStrength.eps_swap`.

-- Generated from ChapterElectroweakFieldStrength.lean — theorem BookProof.ChapterElectroweakFieldStrength.eps_swap
import Definitions.Def_ChapterParity
import Definitions.Def_ChapterParitySU2
import Mathlib
import Definitions.Def_ChapterElectroweakFieldStrength
open BookProof.ChapterElectroweakFieldStrength


open Matrix


open BookProof.ChapterParity BookProof.ChapterParitySU2

theorem BookProof.ChapterElectroweakFieldStrength.eps_swap (a b c : Fin 3) : eps a b c = -eps b a c := by sorry
