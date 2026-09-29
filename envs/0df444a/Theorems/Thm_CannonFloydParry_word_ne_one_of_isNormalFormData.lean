-- Prove2me | Theorems.Thm_CannonFloydParry_word_ne_one_of_isNormalFormData
-- name    : CannonFloydParry.word_ne_one_of_isNormalFormData
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-16T21:13:31.676207+00:00
-- url     : https://prove2.me/theorems/6b0fec16-a764-481f-bc11-eb922e53e1e4
-- title:
--   A normal form is nontrivial
-- statement:
--   If two lists of nonnegative integers satisfy the normal form conditions, then the
--   element
--   $$X_0^{b_0} \cdots X_n^{b_n} \, X_n^{-a_n} \cdots X_0^{-a_0}$$
--   they determine is **not** the identity of $F$.
--
--   This is the converse direction of Corollary-Definition 2.7: not only does every nontrivial
--   element have normal-form data, but every admissible choice of data names a nontrivial
--   element.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, section 2 p. 224, Corollary-Definition 2.7, final sentence

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib

namespace CannonFloydParry

theorem word_ne_one_of_isNormalFormData {as bs : List ℕ} (h : IsNormalFormData as bs) :
    word bs * (word as)⁻¹ ≠ 1 := by
  sorry

end CannonFloydParry
