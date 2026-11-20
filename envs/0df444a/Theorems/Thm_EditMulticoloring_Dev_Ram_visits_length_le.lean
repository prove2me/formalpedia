-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_visits_length_le
-- name    : EditMulticoloring.Dev.Ram.visits_length_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:35:51.6483+00:00
-- url     : https://prove2.me/theorems/40504a09-5a1d-4b5c-9d4d-9aeea8145b66
-- title:
--   EditMulticoloring.Dev.Ram.visits_length_le (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem visits_length_le {q : ℕ} (k : ℕ) (x : Word q) :
--       (visits k x).length ≤ ∑ i ∈ Finset.range (k + 1), (2 * q * (x.length + k + 1)) ^ i
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.visits` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proofs of `EditMulticoloring.Dev.Ram.EncS.mainBody_spec` and `EditMulticoloring.Dev.Ram.visits_le_visBound` of this split import it.
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

theorem visits_length_le {q : ℕ} (k : ℕ) (x : Word q) :
    (visits k x).length ≤ ∑ i ∈ Finset.range (k + 1), (2 * q * (x.length + k + 1)) ^ i := by
  sorry

end EditMulticoloring.Dev.Ram
end
