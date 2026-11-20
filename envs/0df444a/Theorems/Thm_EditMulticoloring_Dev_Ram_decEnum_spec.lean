-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_decEnum_spec
-- name    : EditMulticoloring.Dev.Ram.decEnum_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:32:51.762757+00:00
-- url     : https://prove2.me/theorems/819475fd-adfd-4a47-9d7d-873c396bd8e8
-- title:
--   EditMulticoloring.Dev.Ram.decEnum_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem decEnum_spec {q t n p : ℕ} (H : DHyp q t n p) (hsplit : SplitOK q t n)
--       (z : Word q) (hzl : z.length ≤ n + t) (st : HS) (hI : DInv q t n p none st)
--       (hlen : st.regs ((dC0 t).lenR t) = z.length) (hz : WordAt st ((dC0 t).buf t) 0 z) :
--       DInv q t n p (((scripts t z).map Prod.snd).findSome? (validate t n p))
--         ((enumScripts q t (dC0 t) (pBody q t)).exec inp st) ∧
--       (enumScripts q t (dC0 t) (pBody q t)).cost inp B st ≤
--         (visits t z).length * (dBodyCost q t n B + (dC0 t).enumE B q z.length t)
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.DHyp`, `EditMulticoloring.Dev.Ram.DInv`, `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.SplitOK`, `EditMulticoloring.Dev.Ram.WordAt`, `EditMulticoloring.Dev.Ram.dBodyCost`, `EditMulticoloring.Dev.Ram.dC0`, `EditMulticoloring.Dev.Ram.enumScripts`, `EditMulticoloring.Dev.Ram.pBody`, `EditMulticoloring.Dev.Ram.visits`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec`, `EditMulticoloring.Dev.Ram.EnumCfg.buf`, `EditMulticoloring.Dev.Ram.EnumCfg.enumE` and `EditMulticoloring.Dev.Ram.EnumCfg.lenR` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proof of `EditMulticoloring.Code.ram_programs` of this split imports it.
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

section Body
variable (inp : ℕ → ℕ) (B : ℕ)

theorem decEnum_spec {q t n p : ℕ} (H : DHyp q t n p) (hsplit : SplitOK q t n)
    (z : Word q) (hzl : z.length ≤ n + t) (st : HS) (hI : DInv q t n p none st)
    (hlen : st.regs ((dC0 t).lenR t) = z.length) (hz : WordAt st ((dC0 t).buf t) 0 z) :
    DInv q t n p (((scripts t z).map Prod.snd).findSome? (validate t n p))
      ((enumScripts q t (dC0 t) (pBody q t)).exec inp st) ∧
    (enumScripts q t (dC0 t) (pBody q t)).cost inp B st ≤
      (visits t z).length * (dBodyCost q t n B + (dC0 t).enumE B q z.length t) := by
  sorry

end Body

end EditMulticoloring.Dev.Ram
end
