-- Prove2me | Theorems.Thm_AllOnesGallardo_A071642_terms_ge_two
-- name    : AllOnesGallardo.A071642_terms_ge_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:08:57.79717+00:00
-- url     : https://prove2.me/theorems/b1fce489-4a15-5dd4-8ac3-58206703a454
-- title:
--   All Ones Gallardo: A071642 terms ge two
-- statement:
--   The set-level form of the OEIS A071642 comment: the terms `≥ 2` coincide.
--
--   Source: https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/Solution.lean#L39-L41
-- source:
--   https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/Solution.lean#L39-L41

import Definitions.Def_AllOnesLab
import Definitions.Def_AllOnesComparator_Solution
import Theorems.Thm_AllOnesLab_A071642_terms_ge_two

set_option autoImplicit true
open Polynomial
open AllOnesGallardo

theorem AllOnesGallardo.A071642_terms_ge_two :
    {n : ℕ | 2 ≤ n ∧ Irreducible (allOnes n)} = {n : ℕ | 2 ≤ n ∧ Irreducible (allOnesP n)} := by sorry
