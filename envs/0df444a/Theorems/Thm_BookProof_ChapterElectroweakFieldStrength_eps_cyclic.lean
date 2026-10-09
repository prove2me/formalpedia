-- Prove2me | Theorems.Thm_BookProof_ChapterElectroweakFieldStrength_eps_cyclic
-- name    : BookProof.ChapterElectroweakFieldStrength.eps_cyclic
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T23:14:42.776856+00:00
-- url     : https://prove2.me/theorems/f25ca3bf-7dcc-4819-baa9-9e3fec05c273
-- title:
--   `BookProof.ChapterElectroweakFieldStrength.eps_cyclic` (a b c : Fin 3) : eps a b c = eps c a b
-- statement:
--   Prove the following Lean 4 theorem from `ChapterElectroweakFieldStrength`.
--
--   `BookProof.ChapterElectroweakFieldStrength.eps_cyclic` (a b c : Fin 3) : eps a b c = eps c a b
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterElectroweakFieldStrength.eps_cyclic`.

-- Generated from ChapterElectroweakFieldStrength.lean — theorem BookProof.ChapterElectroweakFieldStrength.eps_cyclic
import Definitions.Def_ChapterParity
import Definitions.Def_ChapterParitySU2
import Mathlib
import Definitions.Def_ChapterElectroweakFieldStrength
open BookProof.ChapterElectroweakFieldStrength


open Matrix


open BookProof.ChapterParity BookProof.ChapterParitySU2

theorem BookProof.ChapterElectroweakFieldStrength.eps_cyclic (a b c : Fin 3) : eps a b c = eps c a b := by sorry
