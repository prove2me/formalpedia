-- Prove2me | Theorems.Thm_FiniteMaximizer__p2m_cf08a975_8aa0_46e9_901e_a88c02c5eb25_a3
-- name    : FiniteMaximizer__p2m_cf08a975_8aa0_46e9_901e_a88c02c5eb25_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:58:30.275076+00:00
-- url     : https://prove2.me/theorems/b45f2ce2-053a-4284-a5f7-467ca267cfa9
-- title:
--   A finite feasible extension family has a maximal maximum
-- statement:
--   In a finite type, among the elements that extend a feasible starting element and satisfy P, choose one maximizing the natural-valued measure w. Reflexivity makes the feasible set nonempty, transitivity keeps further feasible extensions in that set, and strict growth under one-way extension rules out any proper feasible extension of the maximizer. Monotonicity gives the measure lower bound relative to the starting element.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem FiniteMaximizer__p2m_cf08a975_8aa0_46e9_901e_a88c02c5eb25_a3
    {α : Type} [Fintype α] [DecidableEq α]
    (r : α → α → Prop) (P : α → Prop) (w : α → Nat)
    (hrefl : ∀ a, r a a)
    (htrans : ∀ a b c, r a b → r b c → r a c)
    (hmono : ∀ a b, r a b → w a ≤ w b)
    (hstrict : ∀ a b, r a b → ¬ r b a → w a < w b)
    (a : α) (ha : P a) :
    ∃ b, r a b ∧ P b ∧
      (∀ c, r b c → P c → r c b) ∧ w a ≤ w b := by sorry
