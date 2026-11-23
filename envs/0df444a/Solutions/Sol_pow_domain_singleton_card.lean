-- Prove2me | solution 1 for pow_domain_singleton_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:18:01.563247+00:00
-- url     : https://prove2.me/submissions/9dec8110-3c23-4538-a608-1fdfa93c045e

import Mathlib
import Definitions.Def_SimpleRbrFri_Core

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [CommMonoid F] [DecidableEq F] (x : F) (m : ℕ) :
    (pow_domain {x} m).card = 1 := by simp [pow_domain]
