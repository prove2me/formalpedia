-- Prove2me | solution 1 for restrict_eq_iff_eqOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:39:51.247809+00:00
-- url     : https://prove2.me/submissions/ff4de580-d833-4b97-a42a-02a227717fe2

import Mathlib
import Definitions.Def_SimpleRbrFri_Core

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {D S : Type*} (f g : D → S) (s : Set D) :
    s.restrict f = s.restrict g ↔ Set.EqOn f g s :=
  Set.restrict_eq_restrict_iff
