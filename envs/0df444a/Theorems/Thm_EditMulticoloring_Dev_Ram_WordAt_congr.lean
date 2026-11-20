-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_congr
-- name    : EditMulticoloring.Dev.Ram.WordAt.congr
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:32:51.065198+00:00
-- url     : https://prove2.me/theorems/696839cd-6b0d-476f-a598-009955f2e33e
-- title:
--   EditMulticoloring.Dev.Ram.WordAt.congr (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem WordAt.congr {q : ℕ} {s s' : HS} {x off : ℕ} {w : Word q} (h : WordAt s x off w)
--       (h' : ∀ i < w.length, s'.arr x (off + i) = s.arr x (off + i)) : WordAt s' x off w
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.WordAt` and `EditMulticoloring.Dev.Ram.HS.arr` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proofs of `EditMulticoloring.Dev.Ram.EncS.mainBody_spec`, `EditMulticoloring.Dev.Ram.EncS.markEnum_spec`, `EditMulticoloring.Dev.Ram.EnumCfg.delPhase`, `EditMulticoloring.Dev.Ram.EnumCfg.insPhase`, `EditMulticoloring.Dev.Ram.EnumCfg.repPhase`, `EditMulticoloring.Dev.Ram.cBody_spec`, `EditMulticoloring.Dev.Ram.colorInit_spec`, `EditMulticoloring.Dev.Ram.colorOf_spec`, `EditMulticoloring.Dev.Ram.colorsAll_spec`, `EditMulticoloring.Dev.Ram.decEnum_spec`, `EditMulticoloring.Dev.Ram.enBody_spec`, `EditMulticoloring.Dev.Ram.encB_spec`, `EditMulticoloring.Dev.Ram.encG_spec`, `EditMulticoloring.Dev.Ram.encProg_spec`, `EditMulticoloring.Dev.Ram.enumScripts_spec`, `EditMulticoloring.Dev.Ram.pC5_spec`, `EditMulticoloring.Dev.Ram.pC7_spec` and `EditMulticoloring.Dev.Ram.pC8_spec` of this split import it.
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

theorem WordAt.congr {q : ℕ} {s s' : HS} {x off : ℕ} {w : Word q} (h : WordAt s x off w)
    (h' : ∀ i < w.length, s'.arr x (off + i) = s.arr x (off + i)) : WordAt s' x off w := by
  sorry

end EditMulticoloring.Dev.Ram
end
