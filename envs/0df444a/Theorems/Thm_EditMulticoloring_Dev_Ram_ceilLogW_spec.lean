-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_ceilLogW_spec
-- name    : EditMulticoloring.Dev.Ram.ceilLogW_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:32:58.870297+00:00
-- url     : https://prove2.me/theorems/c952f7ba-cc9f-479a-bfa7-f16b52c9b2dd
-- title:
--   EditMulticoloring.Dev.Ram.ceilLogW_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem ceilLogW_spec (b N T S : ℕ) (s : HS) (M : ℕ) (hb : b < S) (hN : N < S) (hT : T < S)
--       (h2 : 2 ≤ s.regs b) (hlog : Nat.log (s.regs b) (s.regs N) ≤ s.regs T)
--       (hM : (s.regs N + 2) * (s.regs b + 1) + s.regs T ≤ M) :
--       ((ceilLogW b N T S).exec inp s).regs S = ceilLog (s.regs b) (s.regs N) ∧
--       ((ceilLogW b N T S).exec inp s).regs (S + 1) = s.regs b ^ ceilLog (s.regs b) (s.regs N) ∧
--       (∀ r', (r' < S ∨ S + 4 ≤ r') → ((ceilLogW b N T S).exec inp s).regs r' = s.regs r') ∧
--       ((ceilLogW b N T S).exec inp s).mem = s.mem ∧
--       ((ceilLogW b N T S).exec inp s).cur = s.cur ∧
--       ((ceilLogW b N T S).exec inp s).out = s.out ∧
--       (ceilLogW b N T S).cost inp B s ≤ (7 * s.regs T + 9) * kappa B (RAM.bits M)
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.ceilLogW`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.Cmd.cost` and `EditMulticoloring.Dev.Ram.Cmd.exec` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proof of `EditMulticoloring.Dev.Ram.pA_spec` of this split imports it.
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

theorem ceilLogW_spec (b N T S : ℕ) (s : HS) (M : ℕ) (hb : b < S) (hN : N < S) (hT : T < S)
    (h2 : 2 ≤ s.regs b) (hlog : Nat.log (s.regs b) (s.regs N) ≤ s.regs T)
    (hM : (s.regs N + 2) * (s.regs b + 1) + s.regs T ≤ M) :
    ((ceilLogW b N T S).exec inp s).regs S = ceilLog (s.regs b) (s.regs N) ∧
    ((ceilLogW b N T S).exec inp s).regs (S + 1) = s.regs b ^ ceilLog (s.regs b) (s.regs N) ∧
    (∀ r', (r' < S ∨ S + 4 ≤ r') → ((ceilLogW b N T S).exec inp s).regs r' = s.regs r') ∧
    ((ceilLogW b N T S).exec inp s).mem = s.mem ∧
    ((ceilLogW b N T S).exec inp s).cur = s.cur ∧
    ((ceilLogW b N T S).exec inp s).out = s.out ∧
    (ceilLogW b N T S).cost inp B s ≤ (7 * s.regs T + 9) * kappa B (RAM.bits M) := by
  sorry

end Logs

end EditMulticoloring.Dev.Ram
end
