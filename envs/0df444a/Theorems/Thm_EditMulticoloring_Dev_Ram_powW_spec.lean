-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_powW_spec
-- name    : EditMulticoloring.Dev.Ram.powW_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:35:20.376015+00:00
-- url     : https://prove2.me/theorems/25b6bcb2-ea0a-4d3f-ae05-0822e2cec339
-- title:
--   EditMulticoloring.Dev.Ram.powW_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem powW_spec (a e S : ℕ) (s : HS) (M : ℕ) (ha : a ≠ S) (he : e ≠ S) (h1 : 1 ≤ s.regs a)
--       (hM : s.regs a ^ s.regs e + s.regs a + s.regs e ≤ M) :
--       ((powW a e S).exec inp s).regs S = s.regs a ^ s.regs e ∧
--       (∀ r', r' ≠ S → ((powW a e S).exec inp s).regs r' = s.regs r') ∧
--       ((powW a e S).exec inp s).mem = s.mem ∧
--       ((powW a e S).exec inp s).cur = s.cur ∧
--       ((powW a e S).exec inp s).out = s.out ∧
--       (powW a e S).cost inp B s ≤ (2 * s.regs e + 3) * kappa B (RAM.bits M)
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.powW`, `EditMulticoloring.Dev.Ram.Cmd.cost` and `EditMulticoloring.Dev.Ram.Cmd.exec` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proofs of `EditMulticoloring.Dev.Ram.decPre_spec`, `EditMulticoloring.Dev.Ram.encE_spec`, `EditMulticoloring.Dev.Ram.paramsW_spec` and `EditMulticoloring.Dev.Ram.radW_spec` of this split import it.
-- source:
--   the submitter, written with Claude, RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds; after the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819)

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000

section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section Logs
variable (inp : ℕ → ℕ) (B : ℕ)

theorem powW_spec (a e S : ℕ) (s : HS) (M : ℕ) (ha : a ≠ S) (he : e ≠ S) (h1 : 1 ≤ s.regs a)
    (hM : s.regs a ^ s.regs e + s.regs a + s.regs e ≤ M) :
    ((powW a e S).exec inp s).regs S = s.regs a ^ s.regs e ∧
    (∀ r', r' ≠ S → ((powW a e S).exec inp s).regs r' = s.regs r') ∧
    ((powW a e S).exec inp s).mem = s.mem ∧
    ((powW a e S).exec inp s).cur = s.cur ∧
    ((powW a e S).exec inp s).out = s.out ∧
    (powW a e S).cost inp B s ≤ (2 * s.regs e + 3) * kappa B (RAM.bits M) := by
  sorry

end Logs

end EditMulticoloring.Dev.Ram
end
