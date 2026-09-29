-- Prove2me | Theorems.Thm_CannonFloydParry_isReduced_iff
-- name    : CannonFloydParry.isReduced_iff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-16T21:12:22.578075+00:00
-- url     : https://prove2.me/theorems/3f0bf7a7-935c-48e2-99e0-da21a3d1c3e3
-- title:
--   Theorem 2.5: when a tree diagram is reduced
-- statement:
--   **Theorem 2.5, second statement.** A tree diagram is reduced if and only if both of
--   the following hold.
--
--   (i) If the last two leaves of the domain tree lie in a common caret, then the last two leaves of
--   the range tree do not.
--
--   (ii) For every $k$ with $k+1$ less than the number of leaves, if the $k$th exponents of the
--   domain and range trees are both positive, then the $(k+1)$th exponent of one of them is
--   positive.
--
--   Exponents past the end of a list read as $0$; the bound on $k$ means that never arises for the
--   indices actually constrained.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, section 2 p. 223, Theorem 2.5, second statement

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib

namespace CannonFloydParry

theorem isReduced_iff (d : TreeDiagram) :
    IsReduced d ↔
      (d.dom.endsInCaret = true → d.ran.endsInCaret = false) ∧
        ∀ k, k + 1 < d.dom.leafCount →
          0 < d.dom.exponents.getD k 0 → 0 < d.ran.exponents.getD k 0 →
            0 < d.dom.exponents.getD (k + 1) 0 ∨ 0 < d.ran.exponents.getD (k + 1) 0 := by
  sorry

end CannonFloydParry
