-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_pC7_spec
-- name    : EditMulticoloring.Dev.Ram.pC7_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:32.731869+00:00
-- url     : https://prove2.me/theorems/b98d868a-0b76-448a-8681-c536aca0db6e
-- title:
--   EditMulticoloring.Dev.Ram.pC7_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem pC7_spec {q t n p : ℕ} (hq : 2 ≤ q) (H3 : (parameters q t n).m + (parameters q t n).ρ = n)
--       (hcol : ∀ y : Word q, localColor t (parameters q t n) p y < (parameters q t n).Q * (parameters q t n).Q + dTW q t n)
--       (st : HS) (hc : DCtx q t n p st) (w : Word q) (hw : WordAt st (dC0 t).a0 0 w)
--       (hwl : w.length = n) (i : ℕ) (hi : st.regs 213 = i) (hiL : i < (parameters q t n).L)
--       (hcx : st.regs 451 = localColor t (parameters q t n) p (w.take (parameters q t n).m))
--       (hV : st.regs 452 = (nbrList t (w.take (parameters q t n).m)).length)
--       (hCL : ∀ ℓ (h : ℓ < (nbrList t (w.take (parameters q t n).m)).length),
--         st.arr 6 ℓ = localColor t (parameters q t n) p (nbrList t (w.take (parameters q t n).m))[ℓ]) :
--       DOut t st ((pC7 t).exec inp st)
--         (if ((List.range i).filter (localGood t (parameters q t n) p (w.take (parameters q t n).m))).length
--             ≥ (parameters q t n).J then none
--          else some (w.take (parameters q t n).m ++ Code.repr q ((parameters q t n).k - (parameters q t n).m)
--             ((List.range i).filter (localGood t (parameters q t n) p (w.take (parameters q t n).m))).length)) ∧
--       (pC7 t).cost inp B st ≤ ((11 * dVb q t n + 11) * (parameters q t n).L + 7 * n + 7 * (parameters q t n).k + 40) *
--         kappa B (RAM.bits (DM q t n))
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.DCtx`, `EditMulticoloring.Dev.Ram.DM`, `EditMulticoloring.Dev.Ram.DOut`, `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.WordAt`, `EditMulticoloring.Dev.Ram.dC0`, `EditMulticoloring.Dev.Ram.dTW`, `EditMulticoloring.Dev.Ram.dVb`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.nbrList`, `EditMulticoloring.Dev.Ram.pC7`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec`, `EditMulticoloring.Dev.Ram.EnumCfg` and `EditMulticoloring.Dev.Ram.HS.arr` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proof of `EditMulticoloring.Dev.Ram.pC5_spec` of this split imports it.
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

theorem pC7_spec {q t n p : ℕ} (hq : 2 ≤ q) (H3 : (parameters q t n).m + (parameters q t n).ρ = n)
    (hcol : ∀ y : Word q, localColor t (parameters q t n) p y < (parameters q t n).Q * (parameters q t n).Q + dTW q t n)
    (st : HS) (hc : DCtx q t n p st) (w : Word q) (hw : WordAt st (dC0 t).a0 0 w)
    (hwl : w.length = n) (i : ℕ) (hi : st.regs 213 = i) (hiL : i < (parameters q t n).L)
    (hcx : st.regs 451 = localColor t (parameters q t n) p (w.take (parameters q t n).m))
    (hV : st.regs 452 = (nbrList t (w.take (parameters q t n).m)).length)
    (hCL : ∀ ℓ (h : ℓ < (nbrList t (w.take (parameters q t n).m)).length),
      st.arr 6 ℓ = localColor t (parameters q t n) p (nbrList t (w.take (parameters q t n).m))[ℓ]) :
    DOut t st ((pC7 t).exec inp st)
      (if ((List.range i).filter (localGood t (parameters q t n) p (w.take (parameters q t n).m))).length
          ≥ (parameters q t n).J then none
       else some (w.take (parameters q t n).m ++ Code.repr q ((parameters q t n).k - (parameters q t n).m)
          ((List.range i).filter (localGood t (parameters q t n) p (w.take (parameters q t n).m))).length)) ∧
    (pC7 t).cost inp B st ≤ ((11 * dVb q t n + 11) * (parameters q t n).L + 7 * n + 7 * (parameters q t n).k + 40) *
      kappa B (RAM.bits (DM q t n)) := by
  sorry

end Levels

end EditMulticoloring.Dev.Ram
end
