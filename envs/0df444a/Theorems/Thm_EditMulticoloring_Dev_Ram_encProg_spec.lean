-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_encProg_spec
-- name    : EditMulticoloring.Dev.Ram.encProg_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:33:43.676464+00:00
-- url     : https://prove2.me/theorems/23a28e5f-9aa0-423b-b8c4-80888efefe4a
-- title:
--   EditMulticoloring.Dev.Ram.encProg_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem encProg_spec (q t n B : ℕ) (hq : 2 ≤ q) (u : FixedWord q (parameters q t n).k)
--       (H1 : ∃ l ≤ n, rhoCond q t (parameters q t n).h l)
--       (H2 : 2 ^ ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) ≤
--           modSearch (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1)) ∧
--         modSearch (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1)) <
--           2 ^ (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1)) :
--       let p := modSearch (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1))
--       let s := (encProg q t).exec (RAM.inputAt (toWord u)) (HS.init n)
--       s.out = (encode t n p (toWord u)).map Fin.val ∧ s.regs encFlag = 1 ∧
--       (encProg q t).cost (RAM.inputAt (toWord u)) B (HS.init n) ≤ encCost q t n B
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.encCost`, `EditMulticoloring.Dev.Ram.encFlag`, `EditMulticoloring.Dev.Ram.encProg`, `EditMulticoloring.Dev.Ram.modSearch`, `EditMulticoloring.Dev.Ram.rhoCond`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec` and `EditMulticoloring.Dev.Ram.HS.init` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proof of `EditMulticoloring.Code.ram_programs` of this split imports it.
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

set_option maxRecDepth 10000 in
theorem encProg_spec (q t n B : ℕ) (hq : 2 ≤ q) (u : FixedWord q (parameters q t n).k)
    (H1 : ∃ l ≤ n, rhoCond q t (parameters q t n).h l)
    (H2 : 2 ^ ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) ≤
        modSearch (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1)) ∧
      modSearch (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1)) <
        2 ^ (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1) + 1)) :
    let p := modSearch (ceilLog 2 ((parameters q t n).r * (parameters q t n).K + 1))
    let s := (encProg q t).exec (RAM.inputAt (toWord u)) (HS.init n)
    s.out = (encode t n p (toWord u)).map Fin.val ∧ s.regs encFlag = 1 ∧
    (encProg q t).cost (RAM.inputAt (toWord u)) B (HS.init n) ≤ encCost q t n B := by
  sorry

end EditMulticoloring.Dev.Ram
end
