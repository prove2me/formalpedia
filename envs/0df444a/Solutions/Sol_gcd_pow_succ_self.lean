-- Prove2me | solution 1 for gcd_pow_succ_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:17:55.241939+00:00
-- url     : https://prove2.me/submissions/946d9963-ae69-4ae1-9dea-58b7b4903dd3

import Mathlib
import Definitions.Def_SimpleRbrFri_Core

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (m k : ℕ) : Nat.gcd (m ^ (k + 1)) m = m :=
  Nat.gcd_eq_right <| dvd_pow_self _ <| Nat.succ_ne_zero _
