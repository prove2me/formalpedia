-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_copyW_word
-- name    : EditMulticoloring.Dev.Ram.copyW_word
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:32:51.975173+00:00
-- url     : https://prove2.me/theorems/635c095e-0fc9-40a9-8978-28283a8a9652
-- title:
--   EditMulticoloring.Dev.Ram.copyW_word (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem copyW_word {q : ℕ} (S so D dO n j t u one : ℕ) (s : HS) (w : Word q)
--       (hreg : [S, so, D, dO, n, j, t, u, one].Nodup) (hSD : s.regs S ≠ s.regs D)
--       (hw : WordAt s (s.regs S) (s.regs so) w) (hn : s.regs n = w.length) :
--       WordAt ((copyW S so D dO n j t u one).exec inp s) (s.regs D) (s.regs dO) w
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.WordAt`, `EditMulticoloring.Dev.Ram.copyW` and `EditMulticoloring.Dev.Ram.Cmd.exec` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proofs of `EditMulticoloring.Dev.Ram.cBody_spec`, `EditMulticoloring.Dev.Ram.colorInit_spec`, `EditMulticoloring.Dev.Ram.colorsAll_spec`, `EditMulticoloring.Dev.Ram.encB_spec`, `EditMulticoloring.Dev.Ram.pC5_spec` and `EditMulticoloring.Dev.Ram.pC8_spec` of this split import it.
-- source:
--   the submitter, written with Claude, RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds; after the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819)

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000

section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section Copy
variable (inp : ℕ → ℕ) (B : ℕ)

theorem copyW_word {q : ℕ} (S so D dO n j t u one : ℕ) (s : HS) (w : Word q)
    (hreg : [S, so, D, dO, n, j, t, u, one].Nodup) (hSD : s.regs S ≠ s.regs D)
    (hw : WordAt s (s.regs S) (s.regs so) w) (hn : s.regs n = w.length) :
    WordAt ((copyW S so D dO n j t u one).exec inp s) (s.regs D) (s.regs dO) w := by
  sorry

end Copy

end EditMulticoloring.Dev.Ram
end
