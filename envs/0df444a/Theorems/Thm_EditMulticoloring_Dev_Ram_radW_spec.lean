-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_radW_spec
-- name    : EditMulticoloring.Dev.Ram.radW_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:35:16.623118+00:00
-- url     : https://prove2.me/theorems/693dfe53-1cf2-4aa2-b7c7-01aeca78ef02
-- title:
--   EditMulticoloring.Dev.Ram.radW_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem radW_spec (q t lR S : ℕ) (s : HS) (M : ℕ) (hl : lR < S) (hq : 1 ≤ q)
--       (hM : radiusBound q (2 * t) (s.regs lR) + 2 * q * (s.regs lR + 2 * t + 1) + 2 * q + 2 * t + 2 ≤ M) :
--       ((radW q t lR S).exec inp s).regs S = radiusBound q (2 * t) (s.regs lR) ∧
--       (∀ r', (r' < S ∨ S + 3 ≤ r') → ((radW q t lR S).exec inp s).regs r' = s.regs r') ∧
--       ((radW q t lR S).exec inp s).mem = s.mem ∧
--       ((radW q t lR S).exec inp s).cur = s.cur ∧
--       ((radW q t lR S).exec inp s).out = s.out ∧
--       (radW q t lR S).cost inp B s ≤ (4 * t + 11) * kappa B (RAM.bits M)
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.radW`, `EditMulticoloring.Dev.Ram.Cmd.cost` and `EditMulticoloring.Dev.Ram.Cmd.exec` (definitions bundle `EMRamB000` of this split).
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

theorem radW_spec (q t lR S : ℕ) (s : HS) (M : ℕ) (hl : lR < S) (hq : 1 ≤ q)
    (hM : radiusBound q (2 * t) (s.regs lR) + 2 * q * (s.regs lR + 2 * t + 1) + 2 * q + 2 * t + 2 ≤ M) :
    ((radW q t lR S).exec inp s).regs S = radiusBound q (2 * t) (s.regs lR) ∧
    (∀ r', (r' < S ∨ S + 3 ≤ r') → ((radW q t lR S).exec inp s).regs r' = s.regs r') ∧
    ((radW q t lR S).exec inp s).mem = s.mem ∧
    ((radW q t lR S).exec inp s).cur = s.cur ∧
    ((radW q t lR S).exec inp s).out = s.out ∧
    (radW q t lR S).cost inp B s ≤ (4 * t + 11) * kappa B (RAM.bits M) := by
  sorry

end Logs

end EditMulticoloring.Dev.Ram
end
