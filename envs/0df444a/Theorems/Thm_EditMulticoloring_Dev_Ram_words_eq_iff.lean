-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_words_eq_iff
-- name    : EditMulticoloring.Dev.Ram.words_eq_iff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:36:05.123459+00:00
-- url     : https://prove2.me/theorems/dc67ba0b-8984-4968-bbd2-6518fcf12b05
-- title:
--   EditMulticoloring.Dev.Ram.words_eq_iff (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem words_eq_iff {q : ℕ} (s : HS) (x ox y oy : ℕ) (w w' : Word q) (hw : WordAt s x ox w)
--       (hw' : WordAt s y oy w') (hl : w.length = w'.length) :
--       (∀ i < w.length, s.arr x (ox + i) = s.arr y (oy + i)) ↔ w = w'
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.WordAt` and `EditMulticoloring.Dev.Ram.HS.arr` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proofs of `EditMulticoloring.Dev.Ram.cBody_spec` and `EditMulticoloring.Dev.Ram.enBody_spec` of this split import it.
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

section Utils
variable (inp : ℕ → ℕ) (B : ℕ)

theorem words_eq_iff {q : ℕ} (s : HS) (x ox y oy : ℕ) (w w' : Word q) (hw : WordAt s x ox w)
    (hw' : WordAt s y oy w') (hl : w.length = w'.length) :
    (∀ i < w.length, s.arr x (ox + i) = s.arr y (oy + i)) ↔ w = w' := by
  sorry

end Utils

end EditMulticoloring.Dev.Ram
end
