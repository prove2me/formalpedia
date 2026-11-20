-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_EncS_reprW_spec
-- name    : EditMulticoloring.Dev.Ram.EncS.reprW_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:31:48.480264+00:00
-- url     : https://prove2.me/theorems/5ae35736-ca70-43eb-aaeb-7b28c9573ddb
-- title:
--   EditMulticoloring.Dev.Ram.EncS.reprW_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram.EncS`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem reprW_spec (r : ℕ) (s : HS) (M : ℕ) (hQ : 0 < s.regs (r + 4))
--       (hP : s.regs (r + 2) = s.regs (r + 4) ^ s.regs (r + 3))
--       (hM : s.regs r + s.regs (r + 1) + s.regs (r + 3) + s.regs (r + 4) +
--         s.regs (r + 4) ^ s.regs (r + 3) ≤ M) :
--       (∀ i < s.regs (r + 3), ((reprW r).exec inp s).arr (s.regs r) i =
--         (s.regs (r + 1) / s.regs (r + 4) ^ (s.regs (r + 3) - 1 - i)) % s.regs (r + 4)) ∧
--       (∀ y i, ¬ (y = s.regs r ∧ i < s.regs (r + 3)) → ((reprW r).exec inp s).arr y i = s.arr y i) ∧
--       (∀ r', r' ≠ r + 2 → r' ≠ r + 5 → r' ≠ r + 6 → r' ≠ r + 7 →
--         ((reprW r).exec inp s).regs r' = s.regs r') ∧
--       ((reprW r).exec inp s).cur = s.cur ∧
--       ((reprW r).exec inp s).out = s.out ∧
--       (reprW r).cost inp B s ≤ (7 * s.regs (r + 3) + 3) * kappa B (RAM.bits M)
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec`, `EditMulticoloring.Dev.Ram.EncS.reprW` and `EditMulticoloring.Dev.Ram.HS.arr` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proofs of `EditMulticoloring.Dev.Ram.EncS.mainBody_spec`, `EditMulticoloring.Dev.Ram.EncS.reprW_word` and `EditMulticoloring.Dev.Ram.encG_spec` of this split import it.
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

theorem reprW_spec (r : ℕ) (s : HS) (M : ℕ) (hQ : 0 < s.regs (r + 4))
    (hP : s.regs (r + 2) = s.regs (r + 4) ^ s.regs (r + 3))
    (hM : s.regs r + s.regs (r + 1) + s.regs (r + 3) + s.regs (r + 4) +
      s.regs (r + 4) ^ s.regs (r + 3) ≤ M) :
    (∀ i < s.regs (r + 3), ((reprW r).exec inp s).arr (s.regs r) i =
      (s.regs (r + 1) / s.regs (r + 4) ^ (s.regs (r + 3) - 1 - i)) % s.regs (r + 4)) ∧
    (∀ y i, ¬ (y = s.regs r ∧ i < s.regs (r + 3)) → ((reprW r).exec inp s).arr y i = s.arr y i) ∧
    (∀ r', r' ≠ r + 2 → r' ≠ r + 5 → r' ≠ r + 6 → r' ≠ r + 7 →
      ((reprW r).exec inp s).regs r' = s.regs r') ∧
    ((reprW r).exec inp s).cur = s.cur ∧
    ((reprW r).exec inp s).out = s.out ∧
    (reprW r).cost inp B s ≤ (7 * s.regs (r + 3) + 3) * kappa B (RAM.bits M) := by
  sorry

end Repr

end EditMulticoloring.Dev.Ram.EncS
end
