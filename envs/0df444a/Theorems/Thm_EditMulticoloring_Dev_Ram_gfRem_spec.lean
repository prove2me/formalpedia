-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_gfRem_spec
-- name    : EditMulticoloring.Dev.Ram.gfRem_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:04.72001+00:00
-- url     : https://prove2.me/theorems/65f69617-48bb-4aaf-b3ac-9f7d9277d1f6
-- title:
--   EditMulticoloring.Dev.Ram.gfRem_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem gfRem_spec (g : ℕ) (s : HS) (M : ℕ) (hp : s.regs g ≠ 0)
--       (hlp : s.regs (g + 1) = (s.regs g).log2) (hP2 : s.regs (g + 2) = 2 ^ (s.regs g).log2)
--       (hPN : s.regs (g + 5) = 2 ^ s.regs (g + 4)) (hz : s.regs (g + 8) < 2 ^ s.regs (g + 4))
--       (hM : s.regs g * 2 ^ s.regs (g + 4) + 4 * 2 ^ s.regs (g + 4) ≤ M) :
--       ((gfRem g).exec inp s).regs (g + 8) = binaryRem (s.regs g) (s.regs (g + 8)) ∧
--       (∀ r', (r' < g + 8 ∨ g + 16 ≤ r') → ((gfRem g).exec inp s).regs r' = s.regs r') ∧
--       ((gfRem g).exec inp s).mem = s.mem ∧
--       ((gfRem g).exec inp s).cur = s.cur ∧
--       ((gfRem g).exec inp s).out = s.out ∧
--       (gfRem g).cost inp B s ≤ (14 * s.regs (g + 4) + 6) * kappa B (RAM.bits M)
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.gfRem`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.Cmd.cost` and `EditMulticoloring.Dev.Ram.Cmd.exec` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proof of `EditMulticoloring.Dev.Ram.gfField_spec` of this split imports it.
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

section Prog
variable (inp : ℕ → ℕ) (B : ℕ)

theorem gfRem_spec (g : ℕ) (s : HS) (M : ℕ) (hp : s.regs g ≠ 0)
    (hlp : s.regs (g + 1) = (s.regs g).log2) (hP2 : s.regs (g + 2) = 2 ^ (s.regs g).log2)
    (hPN : s.regs (g + 5) = 2 ^ s.regs (g + 4)) (hz : s.regs (g + 8) < 2 ^ s.regs (g + 4))
    (hM : s.regs g * 2 ^ s.regs (g + 4) + 4 * 2 ^ s.regs (g + 4) ≤ M) :
    ((gfRem g).exec inp s).regs (g + 8) = binaryRem (s.regs g) (s.regs (g + 8)) ∧
    (∀ r', (r' < g + 8 ∨ g + 16 ≤ r') → ((gfRem g).exec inp s).regs r' = s.regs r') ∧
    ((gfRem g).exec inp s).mem = s.mem ∧
    ((gfRem g).exec inp s).cur = s.cur ∧
    ((gfRem g).exec inp s).out = s.out ∧
    (gfRem g).cost inp B s ≤ (14 * s.regs (g + 4) + 6) * kappa B (RAM.bits M) := by
  sorry

end Prog

end EditMulticoloring.Dev.Ram
end
