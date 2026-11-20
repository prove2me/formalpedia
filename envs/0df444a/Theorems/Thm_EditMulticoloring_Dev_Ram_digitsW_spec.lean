-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_digitsW_spec
-- name    : EditMulticoloring.Dev.Ram.digitsW_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:33:22.839641+00:00
-- url     : https://prove2.me/theorems/46385bb5-ffcc-4402-b287-38c9c46fc3a9
-- title:
--   EditMulticoloring.Dev.Ram.digitsW_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem digitsW_spec (r : ℕ) (s : HS) (M : ℕ)
--       (hM : s.regs r + s.regs (r + 1) + s.regs (r + 2) + s.regs (r + 3) + s.regs (r + 4) ≤ M) :
--       (∀ i < s.regs (r + 2), ((digitsW r).exec inp s).arr (s.regs (r + 3)) (s.regs (r + 4) + i) =
--         (s.regs r / s.regs (r + 1) ^ i) % s.regs (r + 1)) ∧
--       (∀ y i, ¬ (y = s.regs (r + 3) ∧ s.regs (r + 4) ≤ i ∧ i < s.regs (r + 4) + s.regs (r + 2)) →
--         ((digitsW r).exec inp s).arr y i = s.arr y i) ∧
--       (∀ r', (r' < r + 5 ∨ r + 10 ≤ r') → ((digitsW r).exec inp s).regs r' = s.regs r') ∧
--       ((digitsW r).exec inp s).cur = s.cur ∧
--       ((digitsW r).exec inp s).out = s.out ∧
--       (digitsW r).cost inp B s ≤ (7 * s.regs (r + 2) + 4) * kappa B (RAM.bits M)
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.digitsW`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec` and `EditMulticoloring.Dev.Ram.HS.arr` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proof of `EditMulticoloring.Dev.Ram.enBody_spec` of this split imports it.
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

theorem digitsW_spec (r : ℕ) (s : HS) (M : ℕ)
    (hM : s.regs r + s.regs (r + 1) + s.regs (r + 2) + s.regs (r + 3) + s.regs (r + 4) ≤ M) :
    (∀ i < s.regs (r + 2), ((digitsW r).exec inp s).arr (s.regs (r + 3)) (s.regs (r + 4) + i) =
      (s.regs r / s.regs (r + 1) ^ i) % s.regs (r + 1)) ∧
    (∀ y i, ¬ (y = s.regs (r + 3) ∧ s.regs (r + 4) ≤ i ∧ i < s.regs (r + 4) + s.regs (r + 2)) →
      ((digitsW r).exec inp s).arr y i = s.arr y i) ∧
    (∀ r', (r' < r + 5 ∨ r + 10 ≤ r') → ((digitsW r).exec inp s).regs r' = s.regs r') ∧
    ((digitsW r).exec inp s).cur = s.cur ∧
    ((digitsW r).exec inp s).out = s.out ∧
    (digitsW r).cost inp B s ≤ (7 * s.regs (r + 2) + 4) * kappa B (RAM.bits M) := by
  sorry

end Utils

end EditMulticoloring.Dev.Ram
end
