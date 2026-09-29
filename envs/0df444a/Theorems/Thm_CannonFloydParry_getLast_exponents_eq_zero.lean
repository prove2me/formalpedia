-- Prove2me | Theorems.Thm_CannonFloydParry_getLast_exponents_eq_zero
-- name    : CannonFloydParry.getLast_exponents_eq_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-16T21:07:34.155591+00:00
-- url     : https://prove2.me/theorems/55db4b6d-9528-441c-a927-4aa55888614a
-- title:
--   The last exponent of a tree is $0$
-- statement:
--   For every ordered rooted binary tree, the **last** entry of its list of exponents is
--   $0$.
--
--   The exponents are indexed by the leaves in left-to-right order, so this is the exponent of the
--   rightmost leaf. That leaf is a right child of its parent — or, in the one-vertex tree, the root
--   itself — so no arc of left edges begins at it at all, and its exponent is $0$. The restriction
--   about not reaching the right side plays no part here.
--
--   Stated as an equation between options: the last entry of the list, which exists because the list
--   is never empty, is $0$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, section 2 p. 222 (a consequence of the definition of the exponents)

import Definitions.Def_CannonFloydParry_Trees
import Mathlib

namespace CannonFloydParry

theorem getLast_exponents_eq_zero (t : TTree) : t.exponents.getLast? = some 0 := by
  sorry

end CannonFloydParry
