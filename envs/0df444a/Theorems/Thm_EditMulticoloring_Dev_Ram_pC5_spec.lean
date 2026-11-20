-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_pC5_spec
-- name    : EditMulticoloring.Dev.Ram.pC5_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:35.169472+00:00
-- url     : https://prove2.me/theorems/814f1048-7883-4f47-a405-2c2f9d6eb98e
-- title:
--   EditMulticoloring.Dev.Ram.pC5_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem pC5_spec {q t n p : ℕ} (hq : 2 ≤ q) (H3 : (parameters q t n).m + (parameters q t n).ρ = n)
--       (hcol : ∀ y : Word q, localColor t (parameters q t n) p y < (parameters q t n).Q * (parameters q t n).Q + dTW q t n)
--       (hp : p ≠ 0) (hpW : p < dTW q t n) (hQ0 : 0 < (parameters q t n).Q)
--       (hQW : (parameters q t n).Q ≤ dTW q t n)
--       (st : HS) (hc : DCtx q t n p st) (w : Word q) (hw : WordAt st (dC0 t).a0 0 w)
--       (hwl : w.length = n) (i η : ℕ) (hi : st.regs 213 = i) (hiL : i < (parameters q t n).L)
--       (hη : st.regs 214 = η) (hηp : η < primeAt i) (hpi : st.regs 215 = primeAt i) :
--       DOut t st ((pC5 q t).exec inp st) (vTail t (parameters q t n) p (w.take (parameters q t n).m) i η) ∧
--       (pC5 q t).cost inp B st ≤ ((11 * dVb q t n + 11) * (parameters q t n).L + 14 * n +
--         7 * (parameters q t n).k + 11 * dVb q t n + 70) * kappa B (RAM.bits (DM q t n)) + caCost q t n B
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.DCtx`, `EditMulticoloring.Dev.Ram.DM`, `EditMulticoloring.Dev.Ram.DOut`, `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.WordAt`, `EditMulticoloring.Dev.Ram.caCost`, `EditMulticoloring.Dev.Ram.dC0`, `EditMulticoloring.Dev.Ram.dTW`, `EditMulticoloring.Dev.Ram.dVb`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.pC5`, `EditMulticoloring.Dev.Ram.vTail`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec` and `EditMulticoloring.Dev.Ram.EnumCfg` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proof of `EditMulticoloring.Dev.Ram.decEnum_spec` of this split imports it.
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

set_option maxHeartbeats 1600000 in
theorem pC5_spec {q t n p : ℕ} (hq : 2 ≤ q) (H3 : (parameters q t n).m + (parameters q t n).ρ = n)
    (hcol : ∀ y : Word q, localColor t (parameters q t n) p y < (parameters q t n).Q * (parameters q t n).Q + dTW q t n)
    (hp : p ≠ 0) (hpW : p < dTW q t n) (hQ0 : 0 < (parameters q t n).Q)
    (hQW : (parameters q t n).Q ≤ dTW q t n)
    (st : HS) (hc : DCtx q t n p st) (w : Word q) (hw : WordAt st (dC0 t).a0 0 w)
    (hwl : w.length = n) (i η : ℕ) (hi : st.regs 213 = i) (hiL : i < (parameters q t n).L)
    (hη : st.regs 214 = η) (hηp : η < primeAt i) (hpi : st.regs 215 = primeAt i) :
    DOut t st ((pC5 q t).exec inp st) (vTail t (parameters q t n) p (w.take (parameters q t n).m) i η) ∧
    (pC5 q t).cost inp B st ≤ ((11 * dVb q t n + 11) * (parameters q t n).L + 14 * n +
      7 * (parameters q t n).k + 11 * dVb q t n + 70) * kappa B (RAM.bits (DM q t n)) + caCost q t n B := by
  sorry

end Levels

end EditMulticoloring.Dev.Ram
end
