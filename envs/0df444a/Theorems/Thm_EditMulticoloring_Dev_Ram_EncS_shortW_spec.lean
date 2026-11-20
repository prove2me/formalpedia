-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_EncS_shortW_spec
-- name    : EditMulticoloring.Dev.Ram.EncS.shortW_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:31:50.941171+00:00
-- url     : https://prove2.me/theorems/99c30c39-21f1-4856-acca-4ea3785b8d5b
-- title:
--   EditMulticoloring.Dev.Ram.EncS.shortW_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram.EncS`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem shortW_spec {q : ℕ} (hq : 0 < q) (t r a ρ : ℕ) (st : HS)
--       (hρ : st.regs r = ρ) (hN : st.regs (r + 1) = q ^ ρ) :
--       SInv t r a ρ st (greedy t (words q ρ)) ((shortW q t r a).exec inp st) ∧
--       (shortW q t r a).cost inp B st ≤ shortCost B q t ρ a
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec`, `EditMulticoloring.Dev.Ram.EncS.SInv`, `EditMulticoloring.Dev.Ram.EncS.shortCost` and `EditMulticoloring.Dev.Ram.EncS.shortW` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proofs of `EditMulticoloring.Dev.Ram.EncS.shortW_inverse`, `EditMulticoloring.Dev.Ram.decPre_spec` and `EditMulticoloring.Dev.Ram.encF_spec` of this split import it.
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

namespace EditMulticoloring.Dev.Ram.EncS

open EditMulticoloring.Code

section Prog
variable (inp : ℕ → ℕ) (B : ℕ)

set_option maxHeartbeats 1000000 in
theorem shortW_spec {q : ℕ} (hq : 0 < q) (t r a ρ : ℕ) (st : HS)
    (hρ : st.regs r = ρ) (hN : st.regs (r + 1) = q ^ ρ) :
    SInv t r a ρ st (greedy t (words q ρ)) ((shortW q t r a).exec inp st) ∧
    (shortW q t r a).cost inp B st ≤ shortCost B q t ρ a := by
  sorry

end Prog

end EditMulticoloring.Dev.Ram.EncS
end
