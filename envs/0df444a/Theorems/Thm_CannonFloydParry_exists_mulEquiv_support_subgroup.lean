-- Prove2me | Theorems.Thm_CannonFloydParry_exists_mulEquiv_support_subgroup
-- name    : CannonFloydParry.exists_mulEquiv_support_subgroup
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-15T19:30:36.008284+00:00
-- url     : https://prove2.me/theorems/bbe36356-a6a0-4409-8072-92ebfc559fa7
-- title:
--   Elements supported in a dyadic interval form a copy of $F$
-- statement:
--   Let $a$ and $b$ be dyadic rational numbers with $0 \le a < b \le 1$ such that $b-a$ is a
--   power of $2$. Then the set of elements of Thompson's group $F$ whose support is contained in
--   $[a,b]$ is a subgroup of $F$, and it is isomorphic to $F$ itself.
--
--   The support of an element is the set of points of $[0,1]$ that it moves; requiring it to lie in
--   $[a,b]$ is requiring the element to fix every point outside $[a,b]$. The endpoints are
--   permitted: $a$ may be $0$ and $b$ may be $1$. That $b$ is dyadic follows from $a$ being dyadic
--   together with $b - a$ being a power of two, but the source states both, and so does this.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, Lemma 4.4, p. 230

import Definitions.Def_CannonFloydParry
import Mathlib

namespace CannonFloydParry

theorem exists_mulEquiv_support_subgroup {a b : ℝ} (h0 : 0 ≤ a) (hab : a < b) (h1 : b ≤ 1)
    (ha : IsDyadic a) (hb : IsDyadic b) (k : ℤ) (hk : b - a = 2 ^ k) :
    ∃ H : Subgroup F, (∀ g : F, g ∈ H ↔ supp (g : UI ≃o UI) ⊆ Set.Icc a b) ∧
      Nonempty (H ≃* F) := by
  sorry

end CannonFloydParry
