-- Prove2me | Theorems.Thm_Conway99Formal_OwnedTwelve_selected_shell_contacts_20261003
-- name    : Conway99Formal.OwnedTwelve.selected_shell_contacts_20261003
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T00:24:30.184805+00:00
-- url     : https://prove2.me/theorems/905538ac-1f45-49f3-bafa-9d0e4146d351
-- title:
--   Exact contacts for a selected twelve-owner shell
-- statement:
--   Let G be one finite strongly regular graph with parameters (99,14,1,2), and let a,b,c be an actual triangle. Let O be twelve vertices far from all three triangle vertices. Assume each owner has four neighbors in O. Let S be thirty-six vertices outside O and the triangle, with each owner having six neighbors in S. Then every vertex of S has exactly two neighbors in O, and every remaining vertex outside O and the triangle has exactly one neighbor in O. The chosen O and S, their regularity, and their six-incidence condition are explicit premises; this does not construct graph-derived defect owners or identify S with NearF.
-- source:
--   QA-frozen local source formal-owned-twelve commit 2befce26d440bda752c3bf2045da24639017874d, OwnedTwelve.lean SHA256 a2b1c53709374af8647bc589bdab51460b3a46f7670e8ca91d637cf30e7d2134; standalone proof at lab suites/formal-novel/private/OwnedTwelveContactsNoDefs.lean SHA256 107e2ca1233530d842b6bac80306abd887c0c99be71382029f12de78699a23b2. Exact QA receipt run-d19e981907ce at lab snapshot 19722b4916052fc28ffbb4324a2118a234bda1e8: named target and top-level solution compiled under Lean 4.33.1/Mathlib 0df444a with only standard kernel axioms. Conditional necessary theorem for the public Conway99 target, not its resolution.

import Mathlib
set_option autoImplicit false

theorem Conway99Formal.OwnedTwelve.selected_shell_contacts_20261003
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (a b c : V)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (O S : Finset V) (hOcard : O.card = 12)
    (hfar : ∀ z ∈ O, z ≠ a ∧ z ≠ b ∧ z ≠ c ∧
      ¬ G.Adj z a ∧ ¬ G.Adj z b ∧ ¬ G.Adj z c)
    (hregular : ∀ z ∈ O, ((G.neighborFinset z ∩ O).card : ℤ) = 4)
    (hSX : S ⊆ Finset.univ \ (O ∪ ({a, b, c} : Finset V)))
    (hScard : S.card = 36)
    (hsix : ∀ z ∈ O, (G.neighborFinset z ∩ S).card = 6) :
    (∀ z ∈ S, ((G.neighborFinset z ∩ O).card : ℤ) = 2) ∧
      (∀ z ∈ (Finset.univ \ (O ∪ ({a, b, c} : Finset V))) \ S,
        ((G.neighborFinset z ∩ O).card : ℤ) = 1) := by sorry
