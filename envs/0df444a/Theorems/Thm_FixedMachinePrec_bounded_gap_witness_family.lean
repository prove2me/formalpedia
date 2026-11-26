-- Prove2me | Theorems.Thm_FixedMachinePrec_bounded_gap_witness_family
-- name    : FixedMachinePrec.bounded_gap_witness_family
-- status  : Open
-- author  : @kj
-- created : 2026-11-26T12:24:00.725167+00:00
-- url     : https://prove2.me/theorems/061004d4-1d0b-4e2d-ad1a-4a515bb46424
-- title:
--   A family of witness domains closed under smaller marked gaps
-- statement:
--   The structural obligation can be stated without constructing a tree. For a feasible full instance there is a collection of globally representable witness domains containing the whole job set. Each nonempty domain admits a full schedule and increasing marks with globally representable cuts. Every nonempty gap is again in the collection and strictly smaller. The node and cut budgets are respectively $4m+5$ and $m+3$; the collection need not contain every feasible or representable set.
-- source:
--   Auxiliary statement for K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines (1 November 2026), Theorem 5.8, p. 17 and Definition 5.7, p. 15.

import Mathlib
import Definitions.Def_FixedMachinePrec_Formula
import Definitions.Def_FixedMachinePrec_Hierarchy

namespace FixedMachinePrec

theorem bounded_gap_witness_family {N : ℕ} (m : ℕ) (prec : Fin N → Fin N → Prop) [DecidableRel prec] (hm : 3 ≤ m) (hp : IsStrictOrder' prec) (rank : Fin N → ℕ) (hr : IsTopoRank prec rank)
    (hf : ∃ S, IsFullSchedule prec m Finset.univ S) :
    let F := family prec rank m (4*m+5)
    let C := family prec rank m (m+3)
    ∃ D : Finset (Finset (Fin N)), Finset.univ ∈ D ∧ D ⊆ F ∧
      ∀ W ∈ D, W.Nonempty → ∃ S marks, IsFullSchedule prec m W S ∧ marks ≠ [] ∧
        marks.Pairwise (· < ·) ∧ (∀ t ∈ marks, 1 ≤ t ∧ t ≤ S.length) ∧
        (∀ t ∈ marks, ∃ X ∈ C, slotsBetween S 0 t = W ∩ X) ∧
        ∀ A ∈ gaps S marks, A.Nonempty → A ∈ D ∧ A.card < W.card := by sorry

end FixedMachinePrec
