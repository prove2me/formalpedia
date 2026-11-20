-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_modulusW_spec
-- name    : EditMulticoloring.Dev.Ram.modulusW_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:45.515584+00:00
-- url     : https://prove2.me/theorems/83e39329-f831-4cc3-a427-9f54ee04c86f
-- title:
--   EditMulticoloring.Dev.Ram.modulusW_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem modulusW_spec (bR S : ℕ) (s : HS) (M : ℕ) (hb : bR < S)
--       (hM : (2 ^ s.regs bR + 4) * 2 ^ (2 * (s.regs bR + 1)) ≤ M) :
--       ((modulusW bR S).exec inp s).regs S = modSearch (s.regs bR) ∧
--       (∀ r', (r' < S ∨ S + 26 ≤ r') → ((modulusW bR S).exec inp s).regs r' = s.regs r') ∧
--       ((modulusW bR S).exec inp s).mem = s.mem ∧
--       ((modulusW bR S).exec inp s).cur = s.cur ∧
--       ((modulusW bR S).exec inp s).out = s.out ∧
--       (modulusW bR S).cost inp B s ≤
--         (2 ^ s.regs bR + 1) ^ 2 * (44 * s.regs bR + 90) * kappa B (RAM.bits M)
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.modSearch`, `EditMulticoloring.Dev.Ram.modulusW`, `EditMulticoloring.Dev.Ram.Cmd.cost` and `EditMulticoloring.Dev.Ram.Cmd.exec` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proofs of `EditMulticoloring.Dev.Ram.decPre_spec` and `EditMulticoloring.Dev.Ram.encProg_spec` of this split import it.
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

section Modulus
variable (inp : ℕ → ℕ) (B : ℕ)

theorem modulusW_spec (bR S : ℕ) (s : HS) (M : ℕ) (hb : bR < S)
    (hM : (2 ^ s.regs bR + 4) * 2 ^ (2 * (s.regs bR + 1)) ≤ M) :
    ((modulusW bR S).exec inp s).regs S = modSearch (s.regs bR) ∧
    (∀ r', (r' < S ∨ S + 26 ≤ r') → ((modulusW bR S).exec inp s).regs r' = s.regs r') ∧
    ((modulusW bR S).exec inp s).mem = s.mem ∧
    ((modulusW bR S).exec inp s).cur = s.cur ∧
    ((modulusW bR S).exec inp s).out = s.out ∧
    (modulusW bR S).cost inp B s ≤
      (2 ^ s.regs bR + 1) ^ 2 * (44 * s.regs bR + 90) * kappa B (RAM.bits M) := by
  sorry

end Modulus

end EditMulticoloring.Dev.Ram
end
