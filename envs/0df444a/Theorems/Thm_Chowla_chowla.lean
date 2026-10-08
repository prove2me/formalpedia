-- Prove2me | Theorems.Thm_Chowla_chowla
-- name    : Chowla.chowla
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T18:55:01.305449+00:00
-- url     : https://prove2.me/theorems/b13dc9bc-f1f1-4d0c-8f0c-6be789d9727f
-- title:
--   Chowla's theorem (sumset growth in ℤ/m with unit differences)
-- statement:
--   Let m ≥ 1 and let A, B be nonempty subsets of the residue class ring ℤ/m with |A| + |B| ≤ m. Suppose every nonzero difference b − b′ of two elements of B is a unit of ℤ/m. Then the sumset satisfies |A + B| ≥ |A| + |B| − 1. This generalizes the Cauchy–Davenport theorem from prime to composite moduli (where the unit hypothesis replaces primality); it is false without it. Proof is by the Dyson e-transform.
-- source:
--   S. Chowla, A theorem on the addition of residue classes, Proc. Indian Acad. Sci. 2 (1935); see also M. B. Nathanson, Additive Number Theory: Inverse Problems, arXiv:2407.12253 §7 Thm 8

import Mathlib
open scoped Pointwise

namespace Chowla

/-- Chowla's theorem: if `A, B ⊆ ℤ/m` are nonempty with `|A| + |B| ≤ m` and every nonzero
difference of two elements of `B` is a unit, then `|A + B| ≥ |A| + |B| - 1`. -/
theorem chowla {m : ℕ} (hm : 0 < m) {A B : Finset (ZMod m)}
    (hA : A.Nonempty) (hB : B.Nonempty) (hcard : A.card + B.card ≤ m)
    (hunit : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → IsUnit (b - b')) :
    A.card + B.card - 1 ≤ (A + B).card := by
  sorry

end Chowla
