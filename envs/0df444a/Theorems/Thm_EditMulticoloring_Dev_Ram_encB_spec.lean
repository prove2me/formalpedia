-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_encB_spec
-- name    : EditMulticoloring.Dev.Ram.encB_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:33:19.720452+00:00
-- url     : https://prove2.me/theorems/c9426de3-f32d-41cc-b30e-c2784020cc7e
-- title:
--   EditMulticoloring.Dev.Ram.encB_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem encB_spec (q t n p : ℕ) (hq : 2 ≤ q) (w : Word q) (hwl : w.length = (parameters q t n).k)
--       (s : HS) (hs : EBase q t n p s) (hcur : s.cur = 0) :
--       let s' := (encB t q).exec (RAM.inputAt w) s
--       EBase q t n p s' ∧ WordAt s' 2 0 w ∧ WordAt s' (13 + 4 * t) 0 (w.take (parameters q t n).m) ∧
--       s'.regs (307 + 12 * t) = (parameters q t n).m ∧ s'.regs 2 = value (w.drop (parameters q t n).m) ∧
--       s'.cur = (parameters q t n).k ∧ s'.out = s.out ∧
--       (encB t q).cost (RAM.inputAt w) B s ≤
--         (11 * (parameters q t n).k + 7 * (parameters q t n).m + 7 * ((parameters q t n).k - (parameters q t n).m) + 40) *
--           kappa B (RAM.bits (encM q t n))
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.EBase`, `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.WordAt`, `EditMulticoloring.Dev.Ram.encB`, `EditMulticoloring.Dev.Ram.encM`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.Cmd.cost` and `EditMulticoloring.Dev.Ram.Cmd.exec` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proof of `EditMulticoloring.Dev.Ram.encProg_spec` of this split imports it.
-- source:
--   the submitter, written with Claude, RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds; after the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819)

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000

section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section Phases
variable (inp : ℕ → ℕ) (B : ℕ)

theorem encB_spec (q t n p : ℕ) (hq : 2 ≤ q) (w : Word q) (hwl : w.length = (parameters q t n).k)
    (s : HS) (hs : EBase q t n p s) (hcur : s.cur = 0) :
    let s' := (encB t q).exec (RAM.inputAt w) s
    EBase q t n p s' ∧ WordAt s' 2 0 w ∧ WordAt s' (13 + 4 * t) 0 (w.take (parameters q t n).m) ∧
    s'.regs (307 + 12 * t) = (parameters q t n).m ∧ s'.regs 2 = value (w.drop (parameters q t n).m) ∧
    s'.cur = (parameters q t n).k ∧ s'.out = s.out ∧
    (encB t q).cost (RAM.inputAt w) B s ≤
      (11 * (parameters q t n).k + 7 * (parameters q t n).m + 7 * ((parameters q t n).k - (parameters q t n).m) + 40) *
        kappa B (RAM.bits (encM q t n)) := by
  sorry

end Phases

end EditMulticoloring.Dev.Ram
end
