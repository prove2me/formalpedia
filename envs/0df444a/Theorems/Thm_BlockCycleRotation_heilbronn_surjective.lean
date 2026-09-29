-- Prove2me | Theorems.Thm_BlockCycleRotation_heilbronn_surjective
-- name    : BlockCycleRotation.heilbronn_surjective
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:54:25.906759+00:00
-- url     : https://prove2.me/theorems/e335bd85-d539-49e3-bf76-8a00edb90ecc
-- title:
--   Heilbronn's correspondence, surjectivity at the level of quadruples
-- statement:
--   **Heilbronn's correspondence, surjectivity at the level of quadruples.** Every quadruple `(a, b, a', b')` with `a > a' ≥ 1`, `b > b' ≥ 1` and both coprimality conditions arises from a split expansion, and its continuant identity `n = a·b + a'·b'` holds. The suffix is obtained by reversing, which is legitimate by `K_reverse`.
--
--   In Blomer–Bux this is **§4, Heilbronn 1969**, “Heilbronn, surjectivity on quadruples”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4, Heilbronn 1969. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L407-L428

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.heilbronn_surjective {a b a' b' : ℕ}
    (ha : 1 ≤ a') (hab : a' < a) (hga : Nat.gcd a a' = 1)
    (hb : 1 ≤ b') (hbb : b' < b) (hgb : Nat.gcd b b' = 1) :
    ∃ l₁ l₂ : List ℕ, l₁ ≠ [] ∧ l₂ ≠ [] ∧
      K l₁ = a ∧ K l₁.dropLast = a' ∧ K l₂ = b ∧ K l₂.tail = b' ∧
      K (l₁ ++ l₂) = a * b + a' * b' := by sorry
