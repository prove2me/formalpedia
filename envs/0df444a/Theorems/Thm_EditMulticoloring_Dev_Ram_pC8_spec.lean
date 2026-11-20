-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_pC8_spec
-- name    : EditMulticoloring.Dev.Ram.pC8_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:56.94255+00:00
-- url     : https://prove2.me/theorems/c3d30b0a-541c-4731-bb72-bccf6049b2ba
-- title:
--   EditMulticoloring.Dev.Ram.pC8_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem pC8_spec {q t n p : ℕ} (hq : 2 ≤ q) (H3 : (parameters q t n).m + (parameters q t n).ρ = n)
--       (st : HS) (hc : DCtx q t n p st) (w : Word q) (hw : WordAt st (dC0 t).a0 0 w)
--       (hwl : w.length = n) (j : ℕ) (hj : st.regs 240 = j) (hjL : j ≤ (parameters q t n).L) :
--       DOut t st ((pC8 t).exec inp st)
--         (some (w.take (parameters q t n).m ++
--           Code.repr q ((parameters q t n).k - (parameters q t n).m) j)) ∧
--       (pC8 t).cost inp B st ≤ (7 * n + 7 * (parameters q t n).k + 30) * kappa B (RAM.bits (DM q t n))
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.DCtx`, `EditMulticoloring.Dev.Ram.DM`, `EditMulticoloring.Dev.Ram.DOut`, `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.WordAt`, `EditMulticoloring.Dev.Ram.dC0`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.pC8`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec` and `EditMulticoloring.Dev.Ram.EnumCfg` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proof of `EditMulticoloring.Dev.Ram.pC7_spec` of this split imports it.
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

section Levels
variable (inp : ℕ → ℕ) (B : ℕ)

theorem pC8_spec {q t n p : ℕ} (hq : 2 ≤ q) (H3 : (parameters q t n).m + (parameters q t n).ρ = n)
    (st : HS) (hc : DCtx q t n p st) (w : Word q) (hw : WordAt st (dC0 t).a0 0 w)
    (hwl : w.length = n) (j : ℕ) (hj : st.regs 240 = j) (hjL : j ≤ (parameters q t n).L) :
    DOut t st ((pC8 t).exec inp st)
      (some (w.take (parameters q t n).m ++
        Code.repr q ((parameters q t n).k - (parameters q t n).m) j)) ∧
    (pC8 t).cost inp B st ≤ (7 * n + 7 * (parameters q t n).k + 30) * kappa B (RAM.bits (DM q t n)) := by
  sorry

end Levels

end EditMulticoloring.Dev.Ram
end
