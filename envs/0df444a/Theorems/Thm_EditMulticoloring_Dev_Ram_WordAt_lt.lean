-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_lt
-- name    : EditMulticoloring.Dev.Ram.WordAt.lt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:32:32.613207+00:00
-- url     : https://prove2.me/theorems/a9e287a1-0d1f-46bd-8a82-5414879c2609
-- title:
--   EditMulticoloring.Dev.Ram.WordAt.lt (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem WordAt.lt {q : ℕ} {s : HS} {x off : ℕ} {w : Word q} (h : WordAt s x off w) :
--       ∀ i < w.length, s.arr x (off + i) < q
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.WordAt` and `EditMulticoloring.Dev.Ram.HS.arr` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proofs of `EditMulticoloring.Dev.Ram.EncS.markEnum_spec`, `EditMulticoloring.Dev.Ram.EnumCfg.delC_spec`, `EditMulticoloring.Dev.Ram.EnumCfg.insPhase`, `EditMulticoloring.Dev.Ram.EnumCfg.repPhase`, `EditMulticoloring.Dev.Ram.EnumCfg.visitC_spec`, `EditMulticoloring.Dev.Ram.cBody_spec`, `EditMulticoloring.Dev.Ram.colorInit_spec`, `EditMulticoloring.Dev.Ram.colorsAll_spec`, `EditMulticoloring.Dev.Ram.copyW_word`, `EditMulticoloring.Dev.Ram.decEnum_spec`, `EditMulticoloring.Dev.Ram.enBody_spec`, `EditMulticoloring.Dev.Ram.encB_spec`, `EditMulticoloring.Dev.Ram.encG_spec`, `EditMulticoloring.Dev.Ram.pC5_spec`, `EditMulticoloring.Dev.Ram.pC8_spec` and `EditMulticoloring.Dev.Ram.valueW_word` of this split import it.
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

theorem WordAt.lt {q : ℕ} {s : HS} {x off : ℕ} {w : Word q} (h : WordAt s x off w) :
    ∀ i < w.length, s.arr x (off + i) < q := by
  sorry

end EditMulticoloring.Dev.Ram
end
