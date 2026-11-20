-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_upd_eq
-- name    : EditMulticoloring.Dev.Ram.upd_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:30:04.116891+00:00
-- url     : https://prove2.me/theorems/58afd0d0-db7b-4909-b92d-76c8cb5b1f40
-- title:
--   EditMulticoloring.Dev.Ram.upd_eq (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem upd_eq {f : ℕ → ℕ} {a b v : ℕ} (h : b = a) : Function.update f a v b = v
--   ```
--
--   **Used by.** The proofs of `EditMulticoloring.Dev.Ram.EncS.mainBody_spec`, `EditMulticoloring.Dev.Ram.EncS.markEnum_spec`, `EditMulticoloring.Dev.Ram.EncS.reprW_spec`, `EditMulticoloring.Dev.Ram.EnumCfg.delC_spec`, `EditMulticoloring.Dev.Ram.EnumCfg.insPhase`, `EditMulticoloring.Dev.Ram.EnumCfg.repPhase`, `EditMulticoloring.Dev.Ram.cBody_spec`, `EditMulticoloring.Dev.Ram.ceilLogW_spec`, `EditMulticoloring.Dev.Ram.colorInit_spec`, `EditMulticoloring.Dev.Ram.colorSearch_spec`, `EditMulticoloring.Dev.Ram.colorsAll_spec`, `EditMulticoloring.Dev.Ram.decEnum_spec`, `EditMulticoloring.Dev.Ram.decPre_spec`, `EditMulticoloring.Dev.Ram.digitsW_spec`, `EditMulticoloring.Dev.Ram.enBody_spec`, `EditMulticoloring.Dev.Ram.encB_spec`, `EditMulticoloring.Dev.Ram.encG_spec`, `EditMulticoloring.Dev.Ram.eqW_spec`, `EditMulticoloring.Dev.Ram.gfField_spec`, `EditMulticoloring.Dev.Ram.gfRem_spec`, `EditMulticoloring.Dev.Ram.goodW_spec`, `EditMulticoloring.Dev.Ram.pA_spec`, `EditMulticoloring.Dev.Ram.pC5_spec`, `EditMulticoloring.Dev.Ram.pC8_spec`, `EditMulticoloring.Dev.Ram.pPrime_spec`, `EditMulticoloring.Dev.Ram.paramsW_spec`, `EditMulticoloring.Dev.Ram.radW_spec`, `EditMulticoloring.Dev.Ram.readW_spec` and `EditMulticoloring.Dev.Ram.valueW_spec` of this split import it.
-- source:
--   the submitter, written with Claude, RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds; after the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819)

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Machine

section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

theorem upd_eq {f : ℕ → ℕ} {a b v : ℕ} (h : b = a) : Function.update f a v b = v := by
  sorry

end EditMulticoloring.Dev.Ram
end
