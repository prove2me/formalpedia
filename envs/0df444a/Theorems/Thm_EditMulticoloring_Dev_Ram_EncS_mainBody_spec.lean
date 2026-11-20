-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_EncS_mainBody_spec
-- name    : EditMulticoloring.Dev.Ram.EncS.mainBody_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:31:52.331486+00:00
-- url     : https://prove2.me/theorems/74e1274c-0d19-4ca5-acc9-af3ecf3fbe4c
-- title:
--   EditMulticoloring.Dev.Ram.EncS.mainBody_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram.EncS`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem mainBody_spec {q : ℕ} (hq : 0 < q) (t r a ρ : ℕ) (st0 : HS) (k : ℕ) (hk : k < q ^ ρ)
--       (chosen : List (Word q))
--       (hch : chosen = ((List.range k).map (Code.repr q ρ)).foldl (greedyStep t) [])
--       (st : HS) (hS : SInv t r a ρ st0 chosen st) (hj : st.regs (r + 3) = k) :
--       ((mainBody q t r a).exec inp st).regs (r + 3) = k ∧
--       SInv t r a ρ st0 (greedyStep t chosen (Code.repr q ρ k))
--         ((((mainBody q t r a).exec inp st).setR (r + 4) 1).setR (r + 3) (k + 1)) ∧
--       (mainBody q t r a).cost inp B st ≤ mainD B q t ρ a
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec`, `EditMulticoloring.Dev.Ram.EncS.SInv`, `EditMulticoloring.Dev.Ram.EncS.greedyStep`, `EditMulticoloring.Dev.Ram.EncS.mainBody`, `EditMulticoloring.Dev.Ram.EncS.mainD` and `EditMulticoloring.Dev.Ram.HS.setR` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proof of `EditMulticoloring.Dev.Ram.EncS.shortW_spec` of this split imports it.
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

section Main
variable (inp : ℕ → ℕ) (B : ℕ)

set_option maxHeartbeats 1000000 in
theorem mainBody_spec {q : ℕ} (hq : 0 < q) (t r a ρ : ℕ) (st0 : HS) (k : ℕ) (hk : k < q ^ ρ)
    (chosen : List (Word q))
    (hch : chosen = ((List.range k).map (Code.repr q ρ)).foldl (greedyStep t) [])
    (st : HS) (hS : SInv t r a ρ st0 chosen st) (hj : st.regs (r + 3) = k) :
    ((mainBody q t r a).exec inp st).regs (r + 3) = k ∧
    SInv t r a ρ st0 (greedyStep t chosen (Code.repr q ρ k))
      ((((mainBody q t r a).exec inp st).setR (r + 4) 1).setR (r + 3) (k + 1)) ∧
    (mainBody q t r a).cost inp B st ≤ mainD B q t ρ a := by
  sorry

end Main

end EditMulticoloring.Dev.Ram.EncS
end
