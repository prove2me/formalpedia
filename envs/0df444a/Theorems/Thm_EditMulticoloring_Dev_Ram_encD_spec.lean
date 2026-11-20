-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_encD_spec
-- name    : EditMulticoloring.Dev.Ram.encD_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:33:18.643179+00:00
-- url     : https://prove2.me/theorems/9a02b50e-cc74-4109-af9c-f832ddebf949
-- title:
--   EditMulticoloring.Dev.Ram.encD_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem encD_spec (q t n p : ℕ) (s : HS) (hs : EBase q t n p s) (cl : ℕ → ℕ) (X : ℕ)
--       (hcl : ∀ l < s.regs 4, s.arr 6 l = cl l) (hclX : ∀ l < s.regs 4, cl l ≤ X)
--       (h3 : s.regs 3 ≤ X) (h4 : s.regs 4 ≤ X) (h2 : s.regs 2 ≤ X) (hL : (parameters q t n).L ≤ X)
--       (hpb : primeBound (parameters q t n).L ≤ X) :
--       let s' := encD.exec inp s
--       EBase q t n p s' ∧
--       s'.regs 6 = (((List.range (parameters q t n).L).filter
--         (goodTest (s.regs 3) (s.regs 4) cl))[s.regs 2]?).getD (parameters q t n).L ∧
--       s'.regs 2 = s.regs 2 ∧ s'.regs 3 = s.regs 3 ∧ s'.mem = s.mem ∧ s'.cur = s.cur ∧ s'.out = s.out ∧
--       encD.cost inp B s ≤ (3 * ((parameters q t n).L + 1) + (parameters q t n).L * (10 * s.regs 4 + 16) + 3) *
--         kappa B (RAM.bits (8 * X + 8))
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.EBase`, `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.encD`, `EditMulticoloring.Dev.Ram.goodTest`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.primeBound`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec` and `EditMulticoloring.Dev.Ram.HS.arr` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proof of `EditMulticoloring.Dev.Ram.encProg_spec` of this split imports it.
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

section PhaseD
variable (inp : ℕ → ℕ) (B : ℕ)

theorem encD_spec (q t n p : ℕ) (s : HS) (hs : EBase q t n p s) (cl : ℕ → ℕ) (X : ℕ)
    (hcl : ∀ l < s.regs 4, s.arr 6 l = cl l) (hclX : ∀ l < s.regs 4, cl l ≤ X)
    (h3 : s.regs 3 ≤ X) (h4 : s.regs 4 ≤ X) (h2 : s.regs 2 ≤ X) (hL : (parameters q t n).L ≤ X)
    (hpb : primeBound (parameters q t n).L ≤ X) :
    let s' := encD.exec inp s
    EBase q t n p s' ∧
    s'.regs 6 = (((List.range (parameters q t n).L).filter
      (goodTest (s.regs 3) (s.regs 4) cl))[s.regs 2]?).getD (parameters q t n).L ∧
    s'.regs 2 = s.regs 2 ∧ s'.regs 3 = s.regs 3 ∧ s'.mem = s.mem ∧ s'.cur = s.cur ∧ s'.out = s.out ∧
    encD.cost inp B s ≤ (3 * ((parameters q t n).L + 1) + (parameters q t n).L * (10 * s.regs 4 + 16) + 3) *
      kappa B (RAM.bits (8 * X + 8)) := by
  sorry

end PhaseD

end EditMulticoloring.Dev.Ram
end
