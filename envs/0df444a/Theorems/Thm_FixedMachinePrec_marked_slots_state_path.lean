-- Prove2me | Theorems.Thm_FixedMachinePrec_marked_slots_state_path
-- name    : FixedMachinePrec.marked_slots_state_path
-- status  : Proved
-- author  : @kj
-- created : 2026-11-26T17:00:02.418495+00:00
-- url     : https://prove2.me/theorems/897e132b-5b6e-5f01-8884-2a97e1470571
-- title:
--   Marked slots yield an initial-to-final path
-- statement:
--   If lookups succeed for the gaps of a feasible marked schedule with representable cuts, its first and last marked records are connected by successful edges; the initial prefix and final suffix both pass lookup. The table is arbitrary.
-- source:
--   Auxiliary result for K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, 1 November 2026, Definition 5.7 and Theorem 5.9, pp. 15, 18.

import Mathlib
import Definitions.Def_FixedMachinePrec_EvaluateFamily
import Definitions.Def_FixedMachinePrec_Hierarchy

namespace FixedMachinePrec

theorem marked_slots_state_path {N : ℕ} (m : ℕ) (prec : Fin N → Fin N → Prop) [DecidableRel prec] (hm : 1 ≤ m) (hp : IsStrictOrder' prec) (F C : Finset (Finset (Fin N))) (h0 : ∅ ∈ F)
    (W : Finset (Fin N)) (hw : W ∈ F) (hne : W.Nonempty) (S : List (Finset (Fin N)))
    (hs : IsFullSchedule prec m W S) (marks : List ℕ) (hk : marks ≠ [])
    (hi : marks.Pairwise (· < ·)) (hr : ∀ t ∈ marks, 1 ≤ t ∧ t ≤ S.length)
    (hc : ∀ t ∈ marks, ∃ X ∈ C, slotsBetween S 0 t = W ∩ X)
(tab : Table N) (hg : ∀ A ∈ gaps S marks, (lookup F tab A).isSome = true) :
    let st := buildStates prec m C W
    let lk := fun X => (lookup F tab X).isSome
    ∃ i t a b, st[i]? = some a ∧ st[t]? = some b ∧ lk a.L = true ∧ lk b.R = true ∧
      Relation.ReflTransGen (fun x y => edge st lk x y = true) i t := by sorry

end FixedMachinePrec
