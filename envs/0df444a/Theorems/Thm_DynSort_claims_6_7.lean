-- Prove2me | Theorems.Thm_DynSort_claims_6_7
-- name    : DynSort.claims_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:34:26.006661+00:00
-- url     : https://prove2.me/theorems/e58f0d72-bae5-4508-85d9-0979eed7066b
-- title:
--   Claims 6 and 7 — the minimum is in the leftmost cell, the maximum in the rightmost
-- statement:
--   Let $S$ be a level-$i$ DST (a section satisfying the structural invariants) with no hole and at least one element. Then the leftmost cell of $S$ holds an element $m$ with $m\le e$ for every element $e$ of $S$, and the rightmost cell holds an element $M$ with $e\le M$ for every element $e$ of $S$.
--
--   These two facts justify "move $\min X$" by taking the first cell of $X$, and "InsertMax" by filling the last cell.
--
--   **Formalization Note** "Nonempty" is read as storing an element; between operations a DST has no hole (p.10).
--
--   Differences from the source:
--   - encoding: a nonempty i-level DST → a hole-free section satisfying the level-i invariants that stores an element; reason: a DST has no hole in its steady state (p.10)
--   - encoding: elements are distinct reals (ties broken by infinitesimal perturbations, p.11) → elements of ℝ ×ₗ ℕ, a value and an identifier ordered lexicographically; reason: the identifier is the perturbation; every instance of the source is one of these
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), Claims 6–7, p.12 (PDF p.14); proofs pp.44–45 (PDF pp.46–47)

import Mathlib
import Definitions.Def_DynSort_Inv

namespace DynSort

/-- **Claims 6 and 7**, Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §4.2, p.12 (PDF p.14; proofs pp.44–45): "Claim 6. In every
nonempty i-level DST, the minimum element occupies the leftmost cell. They also give the
corresponding property for the maximum element. Claim 7. In every nonempty i-level DST, the
maximum element occupies the rightmost cell."

**Formalization Note.** A level-`i` DST is a section satisfying `Inv i`; "nonempty" means it
stores an element, and a DST between operations has no hole (p.10). Elements are `Elt`. -/
theorem claims_6_7 (i : ℕ) (S : Sec Elt) (hS : Inv i S) (h0 : S.holes = 0)
    (hne : S.stored ≠ []) :
    (∃ m, S.flat.head? = some (some m) ∧ ∀ e ∈ S.stored, m ≤ e) ∧
      (∃ M, S.flat.getLast? = some (some M) ∧ ∀ e ∈ S.stored, e ≤ M) := by sorry

end DynSort
