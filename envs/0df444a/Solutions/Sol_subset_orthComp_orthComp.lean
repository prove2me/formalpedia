-- Prove2me | solution 1 for subset_orthComp_orthComp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T15:07:02.666266+00:00
-- url     : https://prove2.me/submissions/bd25ae2f-6428-4f80-918b-ae82053659cd

import Mathlib
import Definitions.Def_Basic

set_option autoImplicit true
variable {O : Type*} [Orthoset O]
theorem _root_.solution (X : Set O) : X ⊆ orthComp (orthComp X) :=
  fun x hx _ hu => Orthoset.perp_symm (hu x hx)
