-- Prove2me | Theorems.Thm_BlockCycleRotation_K_coprime
-- name    : BlockCycleRotation.K_coprime
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:53:50.151804+00:00
-- url     : https://prove2.me/theorems/4a9fab68-fbe8-47b1-b25d-3271de69b168
-- title:
--   Consecutive continuants are coprime
-- statement:
--   **Consecutive continuants are coprime**: `gcd (K l) (K l.dropLast) = 1`. This supplies the condition `gcd(a, a') = 1` in Heilbronn's correspondence.
--
--   The paper uses this step without giving it a number; the formalization records it as “Consecutive continuants coprime”. It is used in the proofs of `quadExpansion_shift`, `shift_expansion_bijection`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L91-L104

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.K_coprime : ∀ l : List ℕ, Nat.gcd (K l) (K l.dropLast) = 1 := by sorry
