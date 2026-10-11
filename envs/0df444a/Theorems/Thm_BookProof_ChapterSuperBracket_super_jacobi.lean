-- Prove2me | Theorems.Thm_BookProof_ChapterSuperBracket_super_jacobi
-- name    : BookProof.ChapterSuperBracket.super_jacobi
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:05:07.845284+00:00
-- url     : https://prove2.me/theorems/46764858-2575-450e-bc5f-8da810f50957
-- title:
--   `BookProof.ChapterSuperBracket.super_jacobi` (p q r : Bool) (a b c : R) : (eps p r : R) * sbracket p (xor q r) a (sbracket q r b c) + (eps q p : R) * sbracket q (xor r p) b (sbrack
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSuperBracket`.
--
--   `BookProof.ChapterSuperBracket.super_jacobi` (p q r : Bool) (a b c : R) : (eps p r : R) * sbracket p (xor q r) a (sbracket q r b c) + (eps q p : R) * sbracket q (xor r p) b (sbracket r p c a) + (eps r q : R) * sbracket r (xor p q) c (sbracket p q a b) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSuperBracket.super_jacobi`.

-- Generated from ChapterSuperBracket.lean — theorem BookProof.ChapterSuperBracket.super_jacobi
import Mathlib
import Definitions.Def_ChapterSuperBracket
import Definitions.Def_ChapterElectroweakFieldStrength
open BookProof.ChapterElectroweakFieldStrength
open BookProof.ChapterSuperBracket



variable {R : Type*} [Ring R]

theorem BookProof.ChapterSuperBracket.super_jacobi (p q r : Bool) (a b c : R) :
    (eps p r : R) * sbracket p (xor q r) a (sbracket q r b c)
  + (eps q p : R) * sbracket q (xor r p) b (sbracket r p c a)
  + (eps r q : R) * sbracket r (xor p q) c (sbracket p q a b) = 0 := by sorry
