-- Prove2me | Theorems.Thm_CannonFloydParry_isPositive_mul
-- name    : CannonFloydParry.isPositive_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-16T21:14:04.829044+00:00
-- url     : https://prove2.me/theorems/d9227db5-6265-439c-8946-4965625215b5
-- title:
--   Lemma 2.8: positive elements are closed under multiplication
-- statement:
--   **Lemma 2.8.** If $f$ and $g$ are positive elements of $F$ — each a product
--   $X_0^{c_0} X_1^{c_1} \cdots X_n^{c_n}$ with every exponent a nonnegative integer — then so is
--   $f \cdot g$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, section 2 p. 224, Lemma 2.8

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib

namespace CannonFloydParry

theorem isPositive_mul {f g : UI ≃o UI} (hf : IsPositive f) (hg : IsPositive g) :
    IsPositive (f * g) := by
  sorry

end CannonFloydParry
