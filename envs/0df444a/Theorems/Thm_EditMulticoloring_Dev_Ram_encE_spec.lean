-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_encE_spec
-- name    : EditMulticoloring.Dev.Ram.encE_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:33:22.123789+00:00
-- url     : https://prove2.me/theorems/456d09c8-5328-4725-bb3f-3aa34cb31192
-- title:
--   EditMulticoloring.Dev.Ram.encE_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem encE_spec (q t n p : ℕ) (hq : 2 ≤ q) (s : HS) (hs : EBase q t n p s)
--       (hsel : s.regs 6 ≤ (parameters q t n).L)
--       (h3 : s.regs 3 ≤ (parameters q t n).Q ^ 2 + encPW q t n) :
--       let s' := (encE q).exec inp s
--       EBase q t n p s' ∧
--       s'.regs 22 = value (serialize q (parameters q t n) (s.regs 6, s.regs 3 % primeAt (s.regs 6))) ∧
--       s'.mem = s.mem ∧ s'.cur = s.cur ∧ s'.out = s.out ∧
--       (encE q).cost inp B s ≤ (2 * (parameters q t n).h + 13) * kappa B (RAM.bits (encM q t n))
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.EBase`, `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.encE`, `EditMulticoloring.Dev.Ram.encM`, `EditMulticoloring.Dev.Ram.encPW`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.Cmd.cost` and `EditMulticoloring.Dev.Ram.Cmd.exec` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proof of `EditMulticoloring.Dev.Ram.encProg_spec` of this split imports it.
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

section Phases
variable (inp : ℕ → ℕ) (B : ℕ)

theorem encE_spec (q t n p : ℕ) (hq : 2 ≤ q) (s : HS) (hs : EBase q t n p s)
    (hsel : s.regs 6 ≤ (parameters q t n).L)
    (h3 : s.regs 3 ≤ (parameters q t n).Q ^ 2 + encPW q t n) :
    let s' := (encE q).exec inp s
    EBase q t n p s' ∧
    s'.regs 22 = value (serialize q (parameters q t n) (s.regs 6, s.regs 3 % primeAt (s.regs 6))) ∧
    s'.mem = s.mem ∧ s'.cur = s.cur ∧ s'.out = s.out ∧
    (encE q).cost inp B s ≤ (2 * (parameters q t n).h + 13) * kappa B (RAM.bits (encM q t n)) := by
  sorry

end Phases

end EditMulticoloring.Dev.Ram
end
