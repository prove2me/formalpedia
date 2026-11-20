-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_goodW_spec
-- name    : EditMulticoloring.Dev.Ram.goodW_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:05.315222+00:00
-- url     : https://prove2.me/theorems/e9866a8e-4ec2-4e29-86a7-7e095c7184b7
-- title:
--   EditMulticoloring.Dev.Ram.goodW_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem goodW_spec (r piR cxR vR CL : ℕ) (s : HS) (C M : ℕ)
--       (hpi : piR < r ∨ r + 8 ≤ piR) (hcx : cxR < r ∨ r + 8 ≤ cxR) (hv : vR < r ∨ r + 8 ≤ vR)
--       (hC : ∀ ℓ < s.regs vR, s.arr CL ℓ ≤ C)
--       (hM : CL + s.regs vR + C + s.regs cxR + s.regs piR + 1 ≤ M) :
--       ((goodW r piR cxR vR CL).exec inp s).regs r =
--         (if goodP (s.regs cxR) (s.regs piR) (s.arr CL) (s.regs vR) then 1 else 0) ∧
--       (∀ r', (r' < r ∨ r + 8 ≤ r') → ((goodW r piR cxR vR CL).exec inp s).regs r' = s.regs r') ∧
--       ((goodW r piR cxR vR CL).exec inp s).mem = s.mem ∧
--       ((goodW r piR cxR vR CL).exec inp s).cur = s.cur ∧
--       ((goodW r piR cxR vR CL).exec inp s).out = s.out ∧
--       (goodW r piR cxR vR CL).cost inp B s ≤ (11 * s.regs vR + 6) * kappa B (RAM.bits M)
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.goodP`, `EditMulticoloring.Dev.Ram.goodW`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec` and `EditMulticoloring.Dev.Ram.HS.arr` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proofs of `EditMulticoloring.Dev.Ram.pC5_spec` and `EditMulticoloring.Dev.Ram.pC7_spec` of this split import it.
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

section Dec1
variable (inp : ℕ → ℕ) (B : ℕ)

theorem goodW_spec (r piR cxR vR CL : ℕ) (s : HS) (C M : ℕ)
    (hpi : piR < r ∨ r + 8 ≤ piR) (hcx : cxR < r ∨ r + 8 ≤ cxR) (hv : vR < r ∨ r + 8 ≤ vR)
    (hC : ∀ ℓ < s.regs vR, s.arr CL ℓ ≤ C)
    (hM : CL + s.regs vR + C + s.regs cxR + s.regs piR + 1 ≤ M) :
    ((goodW r piR cxR vR CL).exec inp s).regs r =
      (if goodP (s.regs cxR) (s.regs piR) (s.arr CL) (s.regs vR) then 1 else 0) ∧
    (∀ r', (r' < r ∨ r + 8 ≤ r') → ((goodW r piR cxR vR CL).exec inp s).regs r' = s.regs r') ∧
    ((goodW r piR cxR vR CL).exec inp s).mem = s.mem ∧
    ((goodW r piR cxR vR CL).exec inp s).cur = s.cur ∧
    ((goodW r piR cxR vR CL).exec inp s).out = s.out ∧
    (goodW r piR cxR vR CL).cost inp B s ≤ (11 * s.regs vR + 6) * kappa B (RAM.bits M) := by
  sorry

end Dec1

end EditMulticoloring.Dev.Ram
end
