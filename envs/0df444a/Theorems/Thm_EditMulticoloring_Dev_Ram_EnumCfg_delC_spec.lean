-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_EnumCfg_delC_spec
-- name    : EditMulticoloring.Dev.Ram.EnumCfg.delC_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:31:40.070212+00:00
-- url     : https://prove2.me/theorems/c81a053c-a842-44e4-9c93-7ce6c9d69b76
-- title:
--   EditMulticoloring.Dev.Ram.EnumCfg.delC_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram.EnumCfg`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem delC_spec {q : ℕ} (k : ℕ) (x : Word q) (st : HS) (i : ℕ) (hi : i < x.length)
--       (hlen : st.regs (c.lenR (k + 1)) = x.length) (hx : WordAt st (c.buf (k + 1)) 0 x)
--       (hiR : st.regs (c.iR (k + 1)) = i)
--       (M : ℕ) (hM : 2 * c.a0 + 2 * x.length + 2 * k + q + 4 ≤ M) :
--       ((c.delC k).exec inp st).regs (c.lenR k) = (delW x i).length ∧
--       WordAt ((c.delC k).exec inp st) (c.buf k) 0 (delW x i) ∧
--       c.Fr (c.lenR k) (c.buf k) st ((c.delC k).exec inp st) ∧
--       (c.delC k).cost inp B st ≤ (7 * x.length + 20) * kappa B (RAM.bits M)
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.EnumCfg`, `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.WordAt`, `EditMulticoloring.Dev.Ram.delW`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec`, `EditMulticoloring.Dev.Ram.EnumCfg.Fr`, `EditMulticoloring.Dev.Ram.EnumCfg.buf`, `EditMulticoloring.Dev.Ram.EnumCfg.delC`, `EditMulticoloring.Dev.Ram.EnumCfg.iR` and `EditMulticoloring.Dev.Ram.EnumCfg.lenR` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proof of `EditMulticoloring.Dev.Ram.EnumCfg.delPhase` of this split imports it.
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

theorem delC_spec {q : ℕ} (k : ℕ) (x : Word q) (st : HS) (i : ℕ) (hi : i < x.length)
    (hlen : st.regs (c.lenR (k + 1)) = x.length) (hx : WordAt st (c.buf (k + 1)) 0 x)
    (hiR : st.regs (c.iR (k + 1)) = i)
    (M : ℕ) (hM : 2 * c.a0 + 2 * x.length + 2 * k + q + 4 ≤ M) :
    ((c.delC k).exec inp st).regs (c.lenR k) = (delW x i).length ∧
    WordAt ((c.delC k).exec inp st) (c.buf k) 0 (delW x i) ∧
    c.Fr (c.lenR k) (c.buf k) st ((c.delC k).exec inp st) ∧
    (c.delC k).cost inp B st ≤ (7 * x.length + 20) * kappa B (RAM.bits M) := by
  sorry

end EnumCfg

end EditMulticoloring.Dev.Ram
end
