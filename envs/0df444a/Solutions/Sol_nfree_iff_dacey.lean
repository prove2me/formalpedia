-- Prove2me | solution 1 for nfree_iff_dacey
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T15:13:01.878485+00:00
-- url     : https://prove2.me/submissions/60f53c8b-7ded-431d-b4a6-77c8bc8666c3

import Mathlib
import Definitions.Def_Basic
import Theorems.Thm_not_dacey_of_isN
import Theorems.Thm_isN_of_not_dacey

set_option autoImplicit true
variable {O : Type*} [Orthoset O]
variable {P : Type*} [PartialOrder P]
theorem _root_.solution [Finite P] : IsNFree P ↔ IsDacey P := by
  constructor
  · intro hNF
    by_contra hD
    exact hNF (isN_of_not_dacey hD)
  · intro hD ⟨a, b, c, d, hN⟩
    exact not_dacey_of_isN hN hD
