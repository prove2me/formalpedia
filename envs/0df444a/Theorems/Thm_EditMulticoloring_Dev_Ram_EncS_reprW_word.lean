-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_EncS_reprW_word
-- name    : EditMulticoloring.Dev.Ram.EncS.reprW_word
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:31:56.10277+00:00
-- url     : https://prove2.me/theorems/82c4c534-8358-465d-b1ae-8e25ebb01231
-- title:
--   EditMulticoloring.Dev.Ram.EncS.reprW_word (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram.EncS`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem reprW_word {q : ℕ} (hq : 0 < q) (r : ℕ) (s : HS) (hQ : s.regs (r + 4) = q)
--       (hP : s.regs (r + 2) = q ^ s.regs (r + 3)) :
--       WordAt ((reprW r).exec inp s) (s.regs r) 0 (Code.repr q (s.regs (r + 3)) (s.regs (r + 1)))
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.WordAt`, `EditMulticoloring.Dev.Ram.Cmd.exec` and `EditMulticoloring.Dev.Ram.EncS.reprW` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proof of `EditMulticoloring.Dev.Ram.EncS.mainBody_spec` of this split imports it.
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

namespace EditMulticoloring.Dev.Ram.EncS

open EditMulticoloring.Code

section Repr
variable (inp : ℕ → ℕ) (B : ℕ)

theorem reprW_word {q : ℕ} (hq : 0 < q) (r : ℕ) (s : HS) (hQ : s.regs (r + 4) = q)
    (hP : s.regs (r + 2) = q ^ s.regs (r + 3)) :
    WordAt ((reprW r).exec inp s) (s.regs r) 0 (Code.repr q (s.regs (r + 3)) (s.regs (r + 1))) := by
  sorry

end Repr

end EditMulticoloring.Dev.Ram.EncS
end
