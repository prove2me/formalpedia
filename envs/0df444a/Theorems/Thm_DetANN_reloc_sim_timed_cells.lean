-- Prove2me | Theorems.Thm_DetANN_reloc_sim_timed_cells
-- name    : DetANN.reloc_sim_timed_cells
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:54:18.01749+00:00
-- url     : https://prove2.me/theorems/06695a89-4ce9-425b-b82c-f8e2b52a55e4
-- title:
--   Relocated simulation with exact host time and space accounting
-- statement:
--   Assume all the hypotheses of the relocated-simulation theorem `DetANN.reloc_sim_cells`. Thus $P$ halts after $t$ deterministic steps from the virtual state $v$, and $Q$ contains its relocated copy, initially representing $v$ by the host state $r$. There is a host step count $t'$ such that the host reaches the exit label in a running state representing the halted virtual state, the written cells are exactly the base-shifted virtual cells, and moreover
--
--   $$
--   \operatorname{work}(\operatorname{run}(Q,r,\mathrm{detTape},t'))=\operatorname{work}(r)+t',
--   \qquad t'\le 2t.
--   $$
--
--   The simulation relation identifies host work with $c+2\,\operatorname{work}(v)$ at the start and with $c+2\,\operatorname{work}(v_t)$ at the end. Since the virtual run increases work by at most $t$, this yields the stated linear host-time bound. Together with the exact shifted-cell identity, the theorem transfers both time and space estimates from an opaque virtual preprocessing or query program to a relocated call in the composed structure of §7.4.
--
--   **Formalization Note** The bound is sufficient even though the returned $t'$ need not be minimal: all host states through the returned exit state are running, so each of the $t'$ host steps is charged exactly once.
-- source:
--   Original PNormReg relocation-library result written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions'; strengthens DetANN.reloc_sim_cells for the composed construction in Feng--Indyk, STOC 2027 submission, §7.4, p.19. Uses the work equation in PNormRegLib.Agree (definition PNormRegLib_Simulation) and unit work per PNormReg.step.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_AddressBound
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_PNormRegLib_Simulation
import Definitions.Def_DetANN_DataStructure

namespace DetANN

open PNormReg PNormRegLib

/-- In the situation of `reloc_sim_cells`, the returned host run has exact work `r.work + t'`, and
its length is at most twice the virtual run length. -/
theorem reloc_sim_timed_cells (p : RelocParams) (F : Frame) (P Q : Program) (X : ℤ)
    (hE : Embeds Q (reloc p P) p.cOff) (hV : Valid p F) (hU : UsesBelow P F.nR F.nQ)
    (hlit : LitBound P X) (hX : 1 ≤ X) (t : ℕ) (Y : ℤ) (r v : State) (hS : Sim p F r v)
    (hB : PBounded Y v) (hXY : X ≤ Y) (hR : Y * 2 ^ t ≤ F.R)
    (hh : (run P v detTape t).halted = true) :
    ∃ t', Agree p F (run Q r detTape t') (run P v detTape t) ∧
      (run Q r detTape t').core.pc = p.exit ∧ (run Q r detTape t').halted = false ∧
      cellsWritten Q r t' = (cellsWritten P v t).image (fun c => (c.1, F.b + c.2)) ∧
      (run Q r detTape t').work = r.work + t' ∧ t' ≤ 2 * t := by sorry
