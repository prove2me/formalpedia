-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_inputAt_le
-- name    : EditMulticoloring.Dev.Ram.inputAt_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:30:07.301754+00:00
-- url     : https://prove2.me/theorems/5fabc0a3-407b-4244-8675-57b7ae3071bd
-- title:
--   EditMulticoloring.Dev.Ram.inputAt_le (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem inputAt_le {q : ℕ} (y : Word q) (i : ℕ) : RAM.inputAt y i ≤ q
--   ```
--
--   **Used by.** The proofs of `EditMulticoloring.Dev.Ram.decPre_spec` and `EditMulticoloring.Dev.Ram.encB_spec` of this split import it.
-- source:
--   the submitter, written with Claude, RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds; after the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819)

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Machine

section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section Utils
variable (inp : ℕ → ℕ) (B : ℕ)

theorem inputAt_le {q : ℕ} (y : Word q) (i : ℕ) : RAM.inputAt y i ≤ q := by
  sorry

end Utils

end EditMulticoloring.Dev.Ram
end
