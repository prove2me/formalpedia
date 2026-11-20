-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_valueW_spec
-- name    : EditMulticoloring.Dev.Ram.valueW_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:35:51.67375+00:00
-- url     : https://prove2.me/theorems/9f4395cd-45b7-4988-a50f-7ca41a632c82
-- title:
--   EditMulticoloring.Dev.Ram.valueW_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem valueW_spec (r : ℕ) (s : HS) (M : ℕ)
--       (hcell : ∀ i < s.regs (r + 2), s.arr (s.regs r) (s.regs (r + 1) + i) < s.regs (r + 3))
--       (hM : s.regs r + s.regs (r + 1) + s.regs (r + 2) + s.regs (r + 3) +
--         s.regs (r + 3) ^ s.regs (r + 2) ≤ M) :
--       ((valueW r).exec inp s).regs (r + 4) =
--         horner (s.regs (r + 3)) (fun i => s.arr (s.regs r) (s.regs (r + 1) + i)) (s.regs (r + 2)) ∧
--       (∀ r', (r' < r + 4 ∨ r + 9 ≤ r') → ((valueW r).exec inp s).regs r' = s.regs r') ∧
--       ((valueW r).exec inp s).mem = s.mem ∧
--       ((valueW r).exec inp s).cur = s.cur ∧
--       ((valueW r).exec inp s).out = s.out ∧
--       (valueW r).cost inp B s ≤ (7 * s.regs (r + 2) + 4) * kappa B (RAM.bits M)
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.horner`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.valueW`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec` and `EditMulticoloring.Dev.Ram.HS.arr` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proofs of `EditMulticoloring.Dev.Ram.enBody_spec` and `EditMulticoloring.Dev.Ram.valueW_word` of this split import it.
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

theorem valueW_spec (r : ℕ) (s : HS) (M : ℕ)
    (hcell : ∀ i < s.regs (r + 2), s.arr (s.regs r) (s.regs (r + 1) + i) < s.regs (r + 3))
    (hM : s.regs r + s.regs (r + 1) + s.regs (r + 2) + s.regs (r + 3) +
      s.regs (r + 3) ^ s.regs (r + 2) ≤ M) :
    ((valueW r).exec inp s).regs (r + 4) =
      horner (s.regs (r + 3)) (fun i => s.arr (s.regs r) (s.regs (r + 1) + i)) (s.regs (r + 2)) ∧
    (∀ r', (r' < r + 4 ∨ r + 9 ≤ r') → ((valueW r).exec inp s).regs r' = s.regs r') ∧
    ((valueW r).exec inp s).mem = s.mem ∧
    ((valueW r).exec inp s).cur = s.cur ∧
    ((valueW r).exec inp s).out = s.out ∧
    (valueW r).cost inp B s ≤ (7 * s.regs (r + 2) + 4) * kappa B (RAM.bits M) := by
  sorry

end Utils

end EditMulticoloring.Dev.Ram
end
