-- Prove2me | Theorems.Thm_BB5_halt_le_1RB
-- name    : BB5.halt_le_1RB
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-22T15:42:51.630236+00:00
-- url     : https://prove2.me/theorems/977ee1ae-23a0-4c29-9def-77d11c41eeef
-- title:
--   A0 = 1RB: halts within 47,176,870 steps or never
-- statement:
--   Fix a 5-state, two-symbol Turing machine $M$ started on the all-blank tape in state $A$, and suppose its transition $\delta(A,0)$ writes $1$, moves the head **right**, and enters state $B$ -- the Tree Normal Form case called $1RB$. Then either $M$ never halts, or it halts in at most $47{,}176{,}870$ steps.
--
--   This is the second of the two halting-capable branches of the Tree Normal Form case split on the first transition ($0RB$ and $1RB$). Machines whose first transition goes to state $C$, $D$, or $E$ are reduced to this branch by renaming states, and machines whose first transition goes left are reduced to it by reflecting the tape.
--
--   **Formalization Note.** `FCP.BusyBeaver.HaltsIn M c t` asserts that $M$ starting from $c$ performs exactly $t$ transitions, the last of which halts it; the step count includes the final halting transition. The conclusion is the disjunction of perpetual non-halting with the existence of a halting time $t \le 47176870$.
-- source:
--   arXiv:2509.12337 (bbchallenge Collaboration et al., "Determination of the fifth Busy Beaver value"), Section 4 (Tree Normal Form enumeration) and Section 2 (step-count convention).

import Mathlib
import Definitions.Def_FCP_BusyBeaver

namespace BB5

theorem halt_le_1RB (M : FCP.BusyBeaver.TM 5)
    (hA0 : M.trans ⟨0, by omega⟩ false = (true, true, some ⟨1, by omega⟩)) :
    (∀ t : ℕ, FCP.BusyBeaver.run M (FCP.BusyBeaver.init (by omega)) t ≠ none) ∨
      (∃ t : ℕ, t ≤ 47176870 ∧
        FCP.BusyBeaver.HaltsIn M (FCP.BusyBeaver.init (by omega)) t) := by
  sorry

end BB5
