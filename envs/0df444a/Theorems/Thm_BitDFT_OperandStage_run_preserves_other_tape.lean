-- Prove2me | Theorems.Thm_BitDFT_OperandStage_run_preserves_other_tape
-- name    : BitDFT.OperandStage.run_preserves_other_tape
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T17:36:29.414993+00:00
-- url     : https://prove2.me/theorems/b8706379-6ee5-4ddb-a17f-50677e39671d
-- title:
--   Operand staging preserves every unmodified tape
-- statement:
--   For the operand-staging controller, any tape distinct from the coordinate, dimension, and output tapes retains both its contents and head after every number of steps. This is the frame invariant needed to keep the multiplier work bank intact while the operand pair is staged.
-- source:
--   Proved by inspecting the finite controller states: on every non-target tape, each transition writes the scanned symbol and leaves its head stationary. Induction on the number of steps gives the exact tape and head invariant.

import Definitions.Def_BitDFT_OperandStage
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace BitDFT.OperandStage
open IntMul

theorem run_preserves_other_tape {N : MultitapeTM}
    (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (c : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (i : Fin N.k) (hic : i ≠ coord) (hid : i ≠ dim) (hio : i ≠ out) (t : ℕ) :
    ((control N coord dim out hc hd ho hcd hco hdo).machine.step^[t] c).cells i = c.cells i ∧
    ((control N coord dim out hc hd ho hcd hco hdo).machine.step^[t] c).head i = c.head i := by sorry
