-- Prove2me | Theorems.Thm_CannonFloydParry_represents_word_exponents
-- name    : CannonFloydParry.represents_word_exponents
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-16T21:11:50.953881+00:00
-- url     : https://prove2.me/theorems/947282d4-436b-4b14-bc2f-6159e48d877d
-- title:
--   Theorem 2.5: the word of a tree diagram
-- statement:
--   **Theorem 2.5, first statement.** If a tree diagram represents $f$, and $a$ and $b$
--   are the exponent lists of its domain and range trees respectively, then
--   $$f = X_0^{b_0} X_1^{b_1} \cdots X_n^{b_n} \, X_n^{-a_n} \cdots X_1^{-a_1} X_0^{-a_0},$$
--   where $X_0 = A$ and $X_k = A^{-(k-1)} B A^{k-1}$.
--
--   Written here as a product of two words: the positive word read off the range tree's exponents,
--   times the **inverse** of the positive word read off the domain tree's exponents. Those are the
--   same thing, since $\left(X_0^{a_0} \cdots X_n^{a_n}\right)^{-1} = X_n^{-a_n} \cdots
--   X_0^{-a_0}$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, section 2 p. 223, Theorem 2.5, first statement

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib

namespace CannonFloydParry

theorem represents_word_exponents {d : TreeDiagram} {f : UI ≃o UI} (h : Represents d f) :
    f = word d.ran.exponents * (word d.dom.exponents)⁻¹ := by
  sorry

end CannonFloydParry
