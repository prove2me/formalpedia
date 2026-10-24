-- Prove2me | Theorems.Thm_Erdos195_three_complete_annuli_force_fourAP
-- name    : Erdos195.three_complete_annuli_force_fourAP
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T06:48:27.808457+00:00
-- url     : https://prove2.me/theorems/e64f72c9-736c-4327-bcb4-913d8935386c
-- title:
--   Three complete annuli with parity grouping force a four-term progression
-- statement:
--   Let $b\ge4$ be an even integer, and for $j\ge1$ define the complete signed geometric annulus
--   $$A_j=([-b^j,-b^{j-1})\cup[b^{j-1},b^j))\cap\mathbb Z.$$
--   Let $f:\mathbb N\simeq\mathbb Z$ be a permutation. Suppose every element of $A_1$ occurs before every element of $A_2$, and every element of $A_2$ occurs before every element of $A_3$. Suppose also that, within $A_3$, either all odd elements occur before all even elements, or all even elements occur before all odd elements. Then $f$ contains a monotone four-term arithmetic progression.
--
--   No restriction is imposed on the internal orders of $A_1$ or $A_2$, on the order within either parity class of $A_3$, or on the positions of other integers beyond the stated comparisons. In particular, the result excludes chronological concatenation of complete annuli with independently chosen binary-tree orders in the annuli: the root bit of the third annulus's tree order groups its two parity classes.
--
--   This is a structural obstruction to that proposed construction family, not a proof or disproof of the unrestricted Erdős195 existence statement. It is consistent with Adenwalla's five-term-avoidance construction and does not assert a counterexample to any published theorem.
-- source:
--   Research-derived obstruction to a proposed construction family for Erdős Problem195 (https://www.erdosproblems.com/195), directly verified in the canonical Lean model. Contextual motivation: Adenwalla, arXiv:2211.04451v7, Section2, Theorem1, pp3–4, which constructs a five-term-progression-free permutation using complete annuli at base8. The obstruction is not claimed as a theorem of that paper and does not contradict its five-term claim.

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem three_complete_annuli_force_fourAP
    (b : ℤ) (hb : 4 ≤ b) (heven : b % 2 = 0) (f : ℕ ≃ ℤ) :
    let A : ℕ → ℤ → Prop := fun j x =>
      (-b ^ j ≤ x ∧ x < -b ^ (j - 1)) ∨
        (b ^ (j - 1) ≤ x ∧ x < b ^ j)
    (∀ x y, A 1 x → A 2 y → f.symm x < f.symm y) →
    (∀ x y, A 2 x → A 3 y → f.symm x < f.symm y) →
    ((∀ x y, A 3 x → A 3 y → x % 2 = 1 → y % 2 = 0 →
        f.symm x < f.symm y) ∨
      (∀ x y, A 3 x → A 3 y → x % 2 = 0 → y % 2 = 1 →
        f.symm x < f.symm y)) →
    Erdos195.HasMonotoneAP f 4 := by sorry

end Erdos195
