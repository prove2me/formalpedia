-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_CAInv_stable
-- name    : EditMulticoloring.Dev.Ram.CAInv.stable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:31:43.139796+00:00
-- url     : https://prove2.me/theorems/32b9c8a2-e757-4f5f-923e-0e86c371d471
-- title:
--   EditMulticoloring.Dev.Ram.CAInv.stable (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem CAInv.stable {q : ℕ} {t : ℕ} {cfg1 cfg2 : EnumCfg} {g XA DG CLA p Q K : ℕ} {x : Word q}
--       {st0 : HS} (h1r : g + 68 ≤ cfg1.r0) (hCLA : CLA < cfg1.a0)
--       {l : List (Word q)} {st st' : HS} (h : CAInv t cfg1 cfg2 g XA DG CLA p Q K x st0 l st)
--       (hA : cfg1.Agree (2 * t) st st') : CAInv t cfg1 cfg2 g XA DG CLA p Q K x st0 l st'
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.CAInv`, `EditMulticoloring.Dev.Ram.EnumCfg`, `EditMulticoloring.Dev.Ram.HS` and `EditMulticoloring.Dev.Ram.EnumCfg.Agree` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proof of `EditMulticoloring.Dev.Ram.colorsAll_spec` of this split imports it.
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

theorem CAInv.stable {q : ℕ} {t : ℕ} {cfg1 cfg2 : EnumCfg} {g XA DG CLA p Q K : ℕ} {x : Word q}
    {st0 : HS} (h1r : g + 68 ≤ cfg1.r0) (hCLA : CLA < cfg1.a0)
    {l : List (Word q)} {st st' : HS} (h : CAInv t cfg1 cfg2 g XA DG CLA p Q K x st0 l st)
    (hA : cfg1.Agree (2 * t) st st') : CAInv t cfg1 cfg2 g XA DG CLA p Q K x st0 l st' := by
  sorry

end EditMulticoloring.Dev.Ram
end
