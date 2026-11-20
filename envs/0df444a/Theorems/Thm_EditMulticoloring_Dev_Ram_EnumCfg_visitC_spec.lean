-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_EnumCfg_visitC_spec
-- name    : EditMulticoloring.Dev.Ram.EnumCfg.visitC_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:32:08.127179+00:00
-- url     : https://prove2.me/theorems/26781edd-a42c-4840-8dbd-595fcb125da7
-- title:
--   EditMulticoloring.Dev.Ram.EnumCfg.visitC_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram.EnumCfg`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem visitC_spec {q : ℕ} (k : ℕ) (x : Word q) (st : HS) (hlen : st.regs (c.lenR k) = x.length)
--       (hx : WordAt st (c.buf k) 0 x) (M : ℕ) (hM : 2 * c.a0 + 2 * x.length + k + q + 1 ≤ M) :
--       ((c.visitC k).exec inp st).regs c.VL = x.length ∧
--       WordAt ((c.visitC k).exec inp st) c.vis 0 x ∧
--       c.Fr c.VL c.vis st ((c.visitC k).exec inp st) ∧
--       (c.visitC k).cost inp B st ≤ (7 * x.length + 10) * kappa B (RAM.bits M)
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.EnumCfg`, `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.WordAt`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec`, `EditMulticoloring.Dev.Ram.EnumCfg.Fr`, `EditMulticoloring.Dev.Ram.EnumCfg.VL`, `EditMulticoloring.Dev.Ram.EnumCfg.buf`, `EditMulticoloring.Dev.Ram.EnumCfg.lenR`, `EditMulticoloring.Dev.Ram.EnumCfg.vis` and `EditMulticoloring.Dev.Ram.EnumCfg.visitC` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proofs of `EditMulticoloring.Dev.Ram.EnumCfg.lev_zero_spec` and `EditMulticoloring.Dev.Ram.enumScripts_spec` of this split import it.
-- source:
--   the submitter, written with Claude, RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds; after the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819)

import Mathlib
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

namespace EnumCfg
variable (c : EnumCfg) (inp : ℕ → ℕ) (B : ℕ)

theorem visitC_spec {q : ℕ} (k : ℕ) (x : Word q) (st : HS) (hlen : st.regs (c.lenR k) = x.length)
    (hx : WordAt st (c.buf k) 0 x) (M : ℕ) (hM : 2 * c.a0 + 2 * x.length + k + q + 1 ≤ M) :
    ((c.visitC k).exec inp st).regs c.VL = x.length ∧
    WordAt ((c.visitC k).exec inp st) c.vis 0 x ∧
    c.Fr c.VL c.vis st ((c.visitC k).exec inp st) ∧
    (c.visitC k).cost inp B st ≤ (7 * x.length + 10) * kappa B (RAM.bits M) := by
  sorry

end EnumCfg

end EditMulticoloring.Dev.Ram
end
