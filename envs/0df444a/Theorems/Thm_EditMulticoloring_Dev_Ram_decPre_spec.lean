-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_decPre_spec
-- name    : EditMulticoloring.Dev.Ram.decPre_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:33:15.594484+00:00
-- url     : https://prove2.me/theorems/6779e53f-ab7a-42af-b3b4-391809f7bdc6
-- title:
--   EditMulticoloring.Dev.Ram.decPre_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem decPre_spec {q : ℕ} (t n : ℕ) (hq : 2 ≤ q) (y : Word q)
--       (H1 : ∃ l ≤ n, rhoCond q t (parameters q t n).h l)
--       (H2 : modSearch (decB q t n) < dTW q t n)
--       (H3 : (parameters q t n).m + (parameters q t n).ρ = n) :
--       let s := (decPre q t).exec (RAM.inputAt y) (HS.init n)
--       DInv q t n (modSearch (decB q t n)) none s ∧
--       s.regs ((dC0 t).lenR t) = (y.take (n + t + 1)).length ∧
--       WordAt s ((dC0 t).buf t) 0 (y.take (n + t + 1)) ∧
--       s.regs 10 = (if n + t < (y.take (n + t + 1)).length then 1 else 0) +
--         (if (y.take (n + t + 1)).length + t < n then 1 else 0) ∧
--       (decPre q t).cost (RAM.inputAt y) B (HS.init n) ≤ preCost q t n B
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.DInv`, `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.WordAt`, `EditMulticoloring.Dev.Ram.dC0`, `EditMulticoloring.Dev.Ram.dTW`, `EditMulticoloring.Dev.Ram.decB`, `EditMulticoloring.Dev.Ram.decPre`, `EditMulticoloring.Dev.Ram.modSearch`, `EditMulticoloring.Dev.Ram.preCost`, `EditMulticoloring.Dev.Ram.rhoCond`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec`, `EditMulticoloring.Dev.Ram.EnumCfg.buf`, `EditMulticoloring.Dev.Ram.EnumCfg.lenR` and `EditMulticoloring.Dev.Ram.HS.init` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proof of `EditMulticoloring.Code.ram_programs` of this split imports it.
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
set_option linter.unusedVariables false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section Top
variable (B : ℕ)

set_option maxHeartbeats 4000000 in
theorem decPre_spec {q : ℕ} (t n : ℕ) (hq : 2 ≤ q) (y : Word q)
    (H1 : ∃ l ≤ n, rhoCond q t (parameters q t n).h l)
    (H2 : modSearch (decB q t n) < dTW q t n)
    (H3 : (parameters q t n).m + (parameters q t n).ρ = n) :
    let s := (decPre q t).exec (RAM.inputAt y) (HS.init n)
    DInv q t n (modSearch (decB q t n)) none s ∧
    s.regs ((dC0 t).lenR t) = (y.take (n + t + 1)).length ∧
    WordAt s ((dC0 t).buf t) 0 (y.take (n + t + 1)) ∧
    s.regs 10 = (if n + t < (y.take (n + t + 1)).length then 1 else 0) +
      (if (y.take (n + t + 1)).length + t < n then 1 else 0) ∧
    (decPre q t).cost (RAM.inputAt y) B (HS.init n) ≤ preCost q t n B := by
  sorry

end Top

end EditMulticoloring.Dev.Ram
end
