-- Prove2me | solution 1 for orthComp_orthComp_orthComp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T15:08:42.127257+00:00
-- url     : https://prove2.me/submissions/17da09bf-649c-4c07-bda6-7a0742d171bd

import Mathlib
import Definitions.Def_Basic
import Theorems.Thm_orthComp_antitone
import Theorems.Thm_subset_orthComp_orthComp

set_option autoImplicit true
variable {O : Type*} [Orthoset O]
theorem _root_.solution (X : Set O) :
    orthComp (orthComp (orthComp X)) = orthComp X :=
  Set.Subset.antisymm
    (orthComp_antitone (subset_orthComp_orthComp X))
    (subset_orthComp_orthComp (orthComp X))
