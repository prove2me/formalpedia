-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_foldl_listF
-- name    : EditMulticoloring.Dev.Ram.foldl_listF
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:01.005386+00:00
-- url     : https://prove2.me/theorems/8ac49eba-7a78-496d-8758-c7ae34a72d80
-- title:
--   EditMulticoloring.Dev.Ram.foldl_listF (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem foldl_listF {q : ℕ} (x : Word q) (l acc : List (Word q)) :
--       l.foldl (listF x) acc = acc ++ l.filter (fun w => decide (w.length = x.length ∧ w ≠ x))
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.listF` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proofs of `EditMulticoloring.Dev.Ram.colorOf_spec` and `EditMulticoloring.Dev.Ram.colorsAll_spec` of this split import it.
-- source:
--   the submitter, written with Claude, RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds; after the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819)

import Mathlib
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

section Toys
variable (inp : ℕ → ℕ) (B : ℕ)

theorem foldl_listF {q : ℕ} (x : Word q) (l acc : List (Word q)) :
    l.foldl (listF x) acc = acc ++ l.filter (fun w => decide (w.length = x.length ∧ w ≠ x)) := by
  sorry

end Toys

end EditMulticoloring.Dev.Ram
end
