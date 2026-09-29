-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsWord_length_le_three
-- name    : BookProof.NavierStokesFlow.nsWord_length_le_three
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:30:46.245501+00:00
-- url     : https://prove2.me/theorems/6746fd1e-fd74-47b7-8a87-adbd3c267dc8
-- title:
--   The Lean 4 theorem `nsWord_length_le_three` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsWord_length_le_three` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.nsWord_length_le_three
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

theorem BookProof.NavierStokesFlow.nsWord_length_le_three (a : NSWordIndex) : (nsWord a).length ≤ 3 := by sorry
