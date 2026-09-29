-- Prove2me | Theorems.Thm_CannonFloydParry_exists_isNormalFormData_F2
-- name    : CannonFloydParry.exists_isNormalFormData_F2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-17T20:45:31.876459+00:00
-- url     : https://prove2.me/theorems/397f9d4d-e471-4d4c-82b3-f7e2edecaf10
-- title:
--   Every nontrivial element of $F_2$ has a normal form
-- statement:
--   Every element $x \ne 1$ of the presented group $F_2$ can be written as
--   $$x = X_0^{b_0} X_1^{b_1} \cdots X_n^{b_n}\; X_n^{-a_n} \cdots X_1^{-a_1} X_0^{-a_0}$$
--   for lists of nonnegative integers $a = (a_0, \dots, a_n)$, $b = (b_0, \dots, b_n)$ of the same
--   length satisfying the normal-form conditions of Corollary-Definition 2.7 (the predicate
--   `IsNormalFormData` of the §2 bundle): exactly one of $a_n$, $b_n$ is nonzero, and whenever
--   $a_k > 0$ and $b_k > 0$ for some $k < n$, then $a_{k+1} > 0$ or $b_{k+1} > 0$. Here the words are
--   formed in $F_2$ from the symbols $X_i$ (`wordF2`). Existence only: uniqueness of the lists is
--   not asserted (it follows from Theorem 3.4 and the §2 uniqueness theorem).
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 3, p. 226 (proof of Theorem 3.4, second paragraph)

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Definitions.Def_CannonFloydParry_Presentations
import Mathlib

namespace CannonFloydParry

/-- Theorem 3.4, the normal-form step (p. 226): every nontrivial element of `F₂` is a
positive word times the inverse of a positive word whose exponent lists satisfy the
normal-form conditions of Corollary-Definition 2.7. -/
theorem exists_isNormalFormData_F2 (x : F2) (hx : x ≠ 1) :
    ∃ as bs : List ℕ, IsNormalFormData as bs ∧ x = wordF2 bs * (wordF2 as)⁻¹ := by
  sorry

end CannonFloydParry
