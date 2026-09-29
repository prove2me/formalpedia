-- Prove2me | Theorems.Thm_BlockCycleRotation_shift_expansion_bijection
-- name    : BlockCycleRotation.shift_expansion_bijection
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:54:48.290291+00:00
-- url     : https://prove2.me/theorems/89a9ce33-5cfe-4fc6-96c4-bce2cee9314e
-- title:
--   The shift–expansion bijection
-- statement:
--   **The shift–expansion bijection.** For each `n`, the map `k ↦ cf n k` sends the shifts `1 ≤ k` with `2k ≤ n` and `gcd(n,k) = 1` — exactly the range the block cycle algorithm recurses on — to the normalised expansions of `n` whose last entry is at least `2`, i.e. exactly Heilbronn's index set. The inverse is `L ↦ K L.dropLast`. The first component says the forward map lands correctly and is inverted by `L ↦ K L.dropLast`; the second says the backward map lands correctly and is inverted by `k ↦ cf n k`.
--
--   In Blomer–Bux this is **§4**, “Shift ↔ expansion bijection”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L522-L551

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.shift_expansion_bijection (n : ℕ) :
    (∀ k : ℕ, 1 ≤ k → 2 * k ≤ n → Nat.gcd n k = 1 →
        K (cf n k) = n ∧ K (cf n k).dropLast = k ∧ cf n k ≠ []
          ∧ (∀ c ∈ cf n k, 1 ≤ c) ∧ (∀ x ∈ (cf n k).head?, 2 ≤ x)
          ∧ (∀ x ∈ (cf n k).getLast?, 2 ≤ x))
      ∧ (∀ L : List ℕ, L ≠ [] → (∀ c ∈ L, 1 ≤ c) → (∀ x ∈ L.head?, 2 ≤ x) →
        (∀ x ∈ L.getLast?, 2 ≤ x) →
          cf (K L) (K L.dropLast) = L ∧ 1 ≤ K L.dropLast
            ∧ 2 * K L.dropLast ≤ K L ∧ Nat.gcd (K L) (K L.dropLast) = 1) := by sorry
