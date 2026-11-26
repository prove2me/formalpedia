-- Prove2me | Theorems.Thm_FixedMachinePrec_large_gap_witness_domains
-- name    : FixedMachinePrec.large_gap_witness_domains
-- status  : Open
-- author  : @kj
-- created : 2026-11-26T17:00:09.699171+00:00
-- url     : https://prove2.me/theorems/0b8d4590-5ec3-4a44-93cd-bbb437eb6e78
-- title:
--   Witness domains for nodes with more than one full slot
-- statement:
--   For a feasible root, construct globally representable witness domains only for nodes larger than one full slot. Every such domain admits marks with the cut budget $m+3$; each nonempty gap is either another smaller large domain or a single antichain of $m$ jobs. No description or recursive certificate is needed for a terminal antichain.
-- source:
--   Auxiliary result for K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, 1 November 2026, Theorem 5.8 and Definition 5.7, pp. 15–17.

import Mathlib
import Definitions.Def_FixedMachinePrec_Formula
import Definitions.Def_FixedMachinePrec_Hierarchy

namespace FixedMachinePrec

theorem large_gap_witness_domains {N : ℕ} (m : ℕ) (prec : Fin N → Fin N → Prop) [DecidableRel prec] (hm : 3 ≤ m) (hp : IsStrictOrder' prec) (rank : Fin N → ℕ) (hr : IsTopoRank prec rank)
    (hf : ∃ S, IsFullSchedule prec m Finset.univ S) :
let F := family prec rank m (4*m+5)
    let C := family prec rank m (m+3)
    ∃ D : Finset (Finset (Fin N)), (m < N → Finset.univ ∈ D) ∧ D ⊆ F ∧
      ∀ W ∈ D, m < W.card → ∃ S marks, IsFullSchedule prec m W S ∧ marks ≠ [] ∧
        marks.Pairwise (· < ·) ∧ (∀ t ∈ marks, 1 ≤ t ∧ t ≤ S.length) ∧
        (∀ t ∈ marks, ∃ X ∈ C, slotsBetween S 0 t = W ∩ X) ∧
        ∀ A ∈ gaps S marks, A.Nonempty → (A ∈ D ∧ m < A.card ∧ A.card < W.card) ∨
          (A.card = m ∧ IsAntichainSet prec A) := by sorry

end FixedMachinePrec
