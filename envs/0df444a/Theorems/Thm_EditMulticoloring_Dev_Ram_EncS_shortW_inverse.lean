-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_EncS_shortW_inverse
-- name    : EditMulticoloring.Dev.Ram.EncS.shortW_inverse
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:32:04.740124+00:00
-- url     : https://prove2.me/theorems/d362b2d9-3d32-406d-9736-ea7fe9e07ac5
-- title:
--   EditMulticoloring.Dev.Ram.EncS.shortW_inverse (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram.EncS`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem shortW_inverse {q : ℕ} (hq : 0 < q) (t h r a : ℕ) (st : HS)
--       (hρ : st.regs r = shortLength q t h) (hN : st.regs (r + 1) = q ^ shortLength q t h)
--       (z : Word q) :
--       shortInverse t h z =
--         if z.length = shortLength q t h ∧ ((shortW q t r a).exec inp st).arr (a + 2) (value z) ≠ 0 ∧
--             ((shortW q t r a).exec inp st).arr (a + 2) (value z) - 1 < q ^ h
--         then some (Code.repr q h (((shortW q t r a).exec inp st).arr (a + 2) (value z) - 1))
--         else none
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.Cmd.exec`, `EditMulticoloring.Dev.Ram.EncS.shortW` and `EditMulticoloring.Dev.Ram.HS.arr` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proof of `EditMulticoloring.Dev.Ram.decPre_spec` of this split imports it.
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

section Table
variable (inp : ℕ → ℕ)

theorem shortW_inverse {q : ℕ} (hq : 0 < q) (t h r a : ℕ) (st : HS)
    (hρ : st.regs r = shortLength q t h) (hN : st.regs (r + 1) = q ^ shortLength q t h)
    (z : Word q) :
    shortInverse t h z =
      if z.length = shortLength q t h ∧ ((shortW q t r a).exec inp st).arr (a + 2) (value z) ≠ 0 ∧
          ((shortW q t r a).exec inp st).arr (a + 2) (value z) - 1 < q ^ h
      then some (Code.repr q h (((shortW q t r a).exec inp st).arr (a + 2) (value z) - 1))
      else none := by
  sorry

end Table

end EditMulticoloring.Dev.Ram.EncS
end
