-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le
-- name    : EditMulticoloring.Dev.Ram.kappa_bits_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:03.003589+00:00
-- url     : https://prove2.me/theorems/ea992f26-9c61-4817-a4b0-b63433aa2da9
-- title:
--   EditMulticoloring.Dev.Ram.kappa_bits_le (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem kappa_bits_le (B : ℕ) {a M : ℕ} (h : a ≤ M) : kappa B (RAM.bits a) ≤ kappa B (RAM.bits M)
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.kappa` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proofs of `EditMulticoloring.Dev.Ram.EncS.mainBody_spec`, `EditMulticoloring.Dev.Ram.EncS.markEnum_spec`, `EditMulticoloring.Dev.Ram.EncS.reprW_spec`, `EditMulticoloring.Dev.Ram.EncS.shortW_spec`, `EditMulticoloring.Dev.Ram.EnumCfg.delC_spec`, `EditMulticoloring.Dev.Ram.EnumCfg.delPhase`, `EditMulticoloring.Dev.Ram.EnumCfg.insPhase`, `EditMulticoloring.Dev.Ram.EnumCfg.repPhase`, `EditMulticoloring.Dev.Ram.EnumCfg.visitC_spec`, `EditMulticoloring.Dev.Ram.cBody_spec`, `EditMulticoloring.Dev.Ram.ceilLogW_spec`, `EditMulticoloring.Dev.Ram.colorInit_spec`, `EditMulticoloring.Dev.Ram.colorOf_spec`, `EditMulticoloring.Dev.Ram.colorSearch_spec`, `EditMulticoloring.Dev.Ram.colorsAll_spec`, `EditMulticoloring.Dev.Ram.copyW_spec`, `EditMulticoloring.Dev.Ram.decEnum_spec`, `EditMulticoloring.Dev.Ram.decPre_spec`, `EditMulticoloring.Dev.Ram.digitsW_spec`, `EditMulticoloring.Dev.Ram.enBody_spec`, `EditMulticoloring.Dev.Ram.encB_spec`, `EditMulticoloring.Dev.Ram.encD_spec`, `EditMulticoloring.Dev.Ram.encE_spec`, `EditMulticoloring.Dev.Ram.encF_spec`, `EditMulticoloring.Dev.Ram.encG_spec`, `EditMulticoloring.Dev.Ram.encProg_spec`, `EditMulticoloring.Dev.Ram.enumScripts_spec`, `EditMulticoloring.Dev.Ram.eqW_spec`, `EditMulticoloring.Dev.Ram.gfField_spec`, `EditMulticoloring.Dev.Ram.gfRem_spec`, `EditMulticoloring.Dev.Ram.goodW_spec`, `EditMulticoloring.Dev.Ram.pA_spec`, `EditMulticoloring.Dev.Ram.pC5_spec`, `EditMulticoloring.Dev.Ram.pC7_spec`, `EditMulticoloring.Dev.Ram.pC8_spec`, `EditMulticoloring.Dev.Ram.pPrime_spec`, `EditMulticoloring.Dev.Ram.paramsW_spec`, `EditMulticoloring.Dev.Ram.powW_spec`, `EditMulticoloring.Dev.Ram.radW_spec`, `EditMulticoloring.Dev.Ram.readW_spec` and `EditMulticoloring.Dev.Ram.valueW_spec` of this split import it.
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

theorem kappa_bits_le (B : ℕ) {a M : ℕ} (h : a ≤ M) : kappa B (RAM.bits a) ≤ kappa B (RAM.bits M) := by
  sorry

end EditMulticoloring.Dev.Ram
end
