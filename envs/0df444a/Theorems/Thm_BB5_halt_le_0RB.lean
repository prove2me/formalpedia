-- Prove2me | Theorems.Thm_BB5_halt_le_0RB
-- name    : BB5.halt_le_0RB
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-22T15:42:52.919739+00:00
-- url     : https://prove2.me/theorems/d8d93399-cbfe-4b2e-bf1b-d275ef587680
-- title:
--   A0 = 0RB: halts within 47,176,870 steps or never
-- statement:
--   Fix a 5-state, two-symbol Turing machine $M$ started on the all-blank tape in state $A$, and suppose its transition $\delta(A,0)$ writes $0$, moves the head **right**, and enters state $B$ -- the Tree Normal Form case called $0RB$. Then either $M$ never halts, or it halts in at most $47{,}176{,}870$ steps.
--
--   This is one of the three branches of the Tree Normal Form case split on the first transition of a 5-state machine. It is the computational core of the determination of $S(5)$: every machine in this class is either decided non-halting by the decider pipeline or is one of the finitely many halting machines, all of which run for at most the champion's $47{,}176{,}870$ steps.
--
--   **Formalization Note.** `FCP.BusyBeaver.HaltsIn M c t` asserts that $M$ starting from $c$ performs exactly $t$ transitions, the last of which halts it; the step count includes the final halting transition. The conclusion is the disjunction of perpetual non-halting with the existence of a halting time $t \le 47176870$.
-- source:
--   arXiv:2509.12337 (bbchallenge Collaboration et al., "Determination of the fifth Busy Beaver value"), Section 4 (Tree Normal Form enumeration) and Section 2 (step-count convention).

import Mathlib
import Definitions.Def_FCP_BusyBeaver

namespace BB5

theorem halt_le_0RB (M : FCP.BusyBeaver.TM 5)
    (hA0 : M.trans ⟨0, by omega⟩ false = (false, true, some ⟨1, by omega⟩)) :
    (∀ t : ℕ, FCP.BusyBeaver.run M (FCP.BusyBeaver.init (by omega)) t ≠ none) ∨
      (∃ t : ℕ, t ≤ 47176870 ∧
        FCP.BusyBeaver.HaltsIn M (FCP.BusyBeaver.init (by omega)) t) := by
  sorry

end BB5
