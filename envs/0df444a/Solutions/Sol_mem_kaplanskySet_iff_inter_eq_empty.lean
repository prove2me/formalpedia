-- Prove2me | solution 1 for mem_kaplanskySet_iff_inter_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:13:23.158443+00:00
-- url     : https://prove2.me/submissions/115aa14b-971d-4a24-9dfa-cf2701d95d7e

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
import Mathlib.RingTheory.PowerSeries.Ideal
import Definitions.Def_Kaplanski4_Kaplanski

set_option autoImplicit false
variable {R : Type*}
open Set Ideal Submonoid
variable [Semiring R] {S : Subsemigroup R} {P : Ideal R}
theorem _root_.solution : P ∈ kaplanskySet S ↔ (P : Set R) ∩ S = ∅ :=
  disjoint_iff_inter_eq_empty
