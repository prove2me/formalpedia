-- Prove2me | Theorems.Thm_FixedMachinePrec_fill_slot_schedule_with_dummies
-- name    : FixedMachinePrec.fill_slot_schedule_with_dummies
-- status  : Proved
-- author  : @kj
-- created : 2026-11-26T12:24:07.837673+00:00
-- url     : https://prove2.me/theorems/a007761e-7d84-42fb-9f98-29cbb27f9004
-- title:
--   Fill the unused positions of an integral schedule
-- statement:
--   An assignment to $T$ slots respecting precedence and the capacity $m$ extends to a full schedule on $mT$ jobs, by filling the unused positions with isolated dummies. The padded schedule has exactly $T$ slots.
-- source:
--   Auxiliary statement for K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines (1 November 2026), Lemma 5.2, p. 12 and Algorithm 6, p. 10.

import Mathlib
import Definitions.Def_FixedMachinePrec_Deadline

namespace FixedMachinePrec

theorem fill_slot_schedule_with_dummies (G : Instance) (m T : ℕ) (τ : Fin G.n → ℕ) (h : IsSlotSchedule G m T τ) : ∃ S : List (Finset (Fin (m*T))), IsFullSchedule (paddedPrec G (m*T)) m Finset.univ S ∧ S.length = T := by sorry

end FixedMachinePrec
