-- Prove2me | solution 1 for finite_nonempty_subset_has_maximal__p2m_f12881bc_f698_449c_9421_69b4df3ce3de_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:27:17.960119+00:00
-- url     : https://prove2.me/submissions/c4aec503-fcb2-409e-9ccb-810af5fc566f

import Mathlib
set_option autoImplicit false

theorem solution {α : Type} [Fintype α]
    (r : α → α → Prop)
    (hrefl : ∀ a, r a a)
    (htrans : ∀ {a b c}, r a b → r b c → r a c)
    (hanti : ∀ {a b}, r a b → r b a → a = b)
    (S : Set α) (hS : S.Nonempty) :
    ∃ a, S a ∧ ∀ b, S b → r a b → r b a := by
  letI : LE α := ⟨r⟩
  haveI : IsTrans α (· ≤ ·) := ⟨by
    intro a b c hab hbc
    exact htrans hab hbc
  ⟩
  have hfin : S.Finite := Set.toFinite S
  exact hfin.exists_maximal hS