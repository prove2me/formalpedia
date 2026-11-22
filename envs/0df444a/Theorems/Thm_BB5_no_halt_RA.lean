-- Prove2me | Theorems.Thm_BB5_no_halt_RA
-- name    : BB5.no_halt_RA
-- status  : Proved
-- author  : @loader3229
-- created : 2026-11-22T15:42:57.912803+00:00
-- url     : https://prove2.me/theorems/4783a3a6-6431-49d9-9068-c9f350887eeb
-- title:
--   A0 = 0RA or 1RA never halts
-- statement:
--   Fix a 5-state, two-symbol Turing machine $M$ and start it on the all-blank tape in state $A$. Write $\delta(A,0)$ for its transition when state $A$ reads a blank cell. This theorem covers the case in which that transition writes either symbol, moves the head to the **right**, and returns to state $A$ -- the Tree Normal Form cases called $0RA$ and $1RA$. Under this hypothesis $M$ **never halts**: for every number of steps $t$ the configuration after $t$ transitions is still defined.
--
--   Indeed the machine starts in state $A$ scanning a blank cell. Each application of $\delta(A,0)$ writes a symbol, steps one cell to the right, and re-enters state $A$; the cell it now scans is blank, so the same transition fires again. By induction the machine is forever in state $A$ moving right over previously unvisited blank cells, and the undefined (halting) transition is never reached.
--
--   **Formalization Note.** `FCP.BusyBeaver.TM 5` is the type of 5-state two-symbol machines and `⟨0, by omega⟩` is state $A$. A transition is a triple `(write, move, next)` with `move = true` meaning right and `next : Option (Fin 5)`; the hypothesis pins the move to the right and the next state to $A$, leaving the written symbol arbitrary, which is exactly the disjunction $0RA \lor 1RA$. Non-halting is expressed as `run M (init _) t ≠ none` for every $t$.
-- source:
--   arXiv:2509.12337 (bbchallenge Collaboration et al., "Determination of the fifth Busy Beaver value"), Section 4 (Tree Normal Form enumeration) and Section 2 (step-count convention).

import Mathlib
import Definitions.Def_FCP_BusyBeaver

namespace BB5

theorem no_halt_RA (M : FCP.BusyBeaver.TM 5)
    (hA0 : (M.trans ⟨0, by omega⟩ false).2.1 = true ∧
           (M.trans ⟨0, by omega⟩ false).2.2 = some ⟨0, by omega⟩) :
    ∀ t : ℕ, FCP.BusyBeaver.run M (FCP.BusyBeaver.init (by omega)) t ≠ none := by
  sorry

end BB5
