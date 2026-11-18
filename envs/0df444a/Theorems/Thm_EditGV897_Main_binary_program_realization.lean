-- Prove2me | Theorems.Thm_EditGV897_Main_binary_program_realization
-- name    : EditGV897.Main.binary_program_realization
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T04:35:26.926209+00:00
-- url     : https://prove2.me/theorems/13e16903-cad9-40f0-a367-6ac6199c3e04
-- title:
--   Polynomial-time binary machines realized as mission programs
-- statement:
--   Let $f$ be a function between encoded sets, with a polynomial-time certificate in the finite binary multitape-machine model. There is a fixed program in the mission's operational model, and natural constants $A>0,d$, such that every encoded input $a$ has an actual halting execution computing the encoded output $f(a)$ within
--
--   $$A(|a|+1)^d$$
--
--   transitions. The output length has the same bound. The output head is restored to the first bit followed by the prescribed blank terminator. This interface allows finite-machine algorithm certificates to supply the program-realization obligations in the coding construction.
-- source:
--   Gabrys, Singhvi, Yaakobi, Making Every Edit Count, STOC 2027 submission #897, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/897.pdf, Theorem 1 and §4 main proof, printed pp.5,13 / PDF pp.6,14. Operational implementation interface for the specified setup and codec algorithms. Machine models: mission Definitions.Def_EditGV897_Main_Machine (initial, step, execute, Runs); Cslib/Complexitylib finite multitape Turing model, github.com/raresbuhai/formalization-of-my-research @ 7abf511, Computability/Machines/Turing/MultiTape, as mirrored by Prove2Me.

import Definitions.Def_EditGV897_Main_Codec
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Plain
open EditGV897.Main

theorem EditGV897.Main.binary_program_realization {α β : Type} (f : α → β)
    (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (hf : Turing.MultiTapeTM.ComputableInPolyTime f encIn encOut) :
    ∃ (P : Program) (A d : ℕ), 0 < A ∧ ∀ a : α,
      Runs P (encIn a) (encOut (f a)) (polyBudget A d (encIn a).length) ∧
      (encOut (f a)).length ≤ polyBudget A d (encIn a).length := by sorry
