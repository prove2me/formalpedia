-- Prove2me | solution 1 for markov_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:53:02.993758+00:00
-- url     : https://prove2.me/submissions/d4467121-da87-4772-bf22-6890dfd7958d

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_Polychromatic_DiscreteProbability
import Theorems.Thm_markov

set_option autoImplicit true
open Finset
variable {ι α : Type*} {s : Finset ι} {p f : ι → α} {c : α} [LinearOrder α]
theorem _root_.solution [DivisionRing α] [IsStrictOrderedRing α]
    (hp : ∀ i ∈ s, 0 ≤ p i) (hc : 0 < c) :
    ∑ i ∈ s with c ≤ |f i|, p i ≤ (∑ i ∈ s, p i * |f i|) / c :=
  markov hp (by simp) hc
