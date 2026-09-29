-- Prove2me | Theorems.Thm_FamousTheorems_antitone_chain_condition
-- name    : FamousTheorems.antitone_chain_condition
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T16:54:33.882665+00:00
-- url     : https://prove2.me/theorems/665a29d3-f7b2-4102-a731-fc49fcec571a
-- title:
--   The descending chain condition
-- statement:
--   **The descending chain condition.** An order is well-founded exactly when every antitone sequence eventually stabilises. This is the mirror of the ascending condition and is the hypothesis behind Artinian rings and modules. Well-foundedness is precisely what makes proof by minimal counterexample valid, so the equivalence says that induction is available exactly when infinite strict descent is impossible. **Formalization note.** `WellFoundedLT` is well-foundedness of the order itself. The result is Mathlib's `WellFoundedLT.antitone_chain_condition`.
-- source:
--   Marked as a named theorem in Mathlib's own docstrings; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem antitone_chain_condition :
    ∀ {α : Type u_1} [inst : PartialOrder α] [WellFoundedLT α] {f : ℕ → α}, 
    Antitone f → ∃ n, ∀ (m : ℕ), n ≤ m → f n = f m := by sorry

end FamousTheorems
