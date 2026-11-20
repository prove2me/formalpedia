-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_pA_spec
-- name    : EditMulticoloring.Dev.Ram.pA_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:36.408786+00:00
-- url     : https://prove2.me/theorems/6ce6e153-a3c8-4195-9a84-f65b8bbd7765
-- title:
--   EditMulticoloring.Dev.Ram.pA_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem pA_spec (q t nR O : ℕ) (s : HS) (M : ℕ) (hq : 2 ≤ q) (hn : nR < O)
--       (hM : pABound q t (s.regs nR) ≤ M) :
--       ((pA q t nR O).exec inp s).regs O = (parameters q t (s.regs nR)).r ∧
--       ((pA q t nR O).exec inp s).regs (O + 1) = (parameters q t (s.regs nR)).K ∧
--       ((pA q t nR O).exec inp s).regs (O + 2) =
--         ceilLog 2 ((parameters q t (s.regs nR)).r * (parameters q t (s.regs nR)).K + 1) ∧
--       ((pA q t nR O).exec inp s).regs (O + 3) = (parameters q t (s.regs nR)).Q ∧
--       ((pA q t nR O).exec inp s).regs (O + 4) = (parameters q t (s.regs nR)).B ∧
--       ((pA q t nR O).exec inp s).regs (O + 5) = (parameters q t (s.regs nR)).L ∧
--       ((pA q t nR O).exec inp s).regs (O + 6) =
--         ceilLog 2 ((parameters q t (s.regs nR)).r * (parameters q t (s.regs nR)).K + 1) + 1 ∧
--       (∀ r', (r' < O ∨ (O + 7 ≤ r' ∧ r' < O + 17) ∨ O + 49 ≤ r') →
--         ((pA q t nR O).exec inp s).regs r' = s.regs r') ∧
--       ((pA q t nR O).exec inp s).mem = s.mem ∧
--       ((pA q t nR O).exec inp s).cur = s.cur ∧
--       ((pA q t nR O).exec inp s).out = s.out ∧
--       (pA q t nR O).cost inp B s ≤
--         (7 * ((parameters q t (s.regs nR)).r * (parameters q t (s.regs nR)).K + 1) + 4 * t + 40) *
--           kappa B (RAM.bits M)
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.pA`, `EditMulticoloring.Dev.Ram.pABound`, `EditMulticoloring.Dev.Ram.Cmd.cost` and `EditMulticoloring.Dev.Ram.Cmd.exec` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proof of `EditMulticoloring.Dev.Ram.paramsW_spec` of this split imports it.
-- source:
--   the submitter, written with Claude, RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds; after the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819)

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000

section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section PartA
variable (inp : ℕ → ℕ) (B : ℕ)

theorem pA_spec (q t nR O : ℕ) (s : HS) (M : ℕ) (hq : 2 ≤ q) (hn : nR < O)
    (hM : pABound q t (s.regs nR) ≤ M) :
    ((pA q t nR O).exec inp s).regs O = (parameters q t (s.regs nR)).r ∧
    ((pA q t nR O).exec inp s).regs (O + 1) = (parameters q t (s.regs nR)).K ∧
    ((pA q t nR O).exec inp s).regs (O + 2) =
      ceilLog 2 ((parameters q t (s.regs nR)).r * (parameters q t (s.regs nR)).K + 1) ∧
    ((pA q t nR O).exec inp s).regs (O + 3) = (parameters q t (s.regs nR)).Q ∧
    ((pA q t nR O).exec inp s).regs (O + 4) = (parameters q t (s.regs nR)).B ∧
    ((pA q t nR O).exec inp s).regs (O + 5) = (parameters q t (s.regs nR)).L ∧
    ((pA q t nR O).exec inp s).regs (O + 6) =
      ceilLog 2 ((parameters q t (s.regs nR)).r * (parameters q t (s.regs nR)).K + 1) + 1 ∧
    (∀ r', (r' < O ∨ (O + 7 ≤ r' ∧ r' < O + 17) ∨ O + 49 ≤ r') →
      ((pA q t nR O).exec inp s).regs r' = s.regs r') ∧
    ((pA q t nR O).exec inp s).mem = s.mem ∧
    ((pA q t nR O).exec inp s).cur = s.cur ∧
    ((pA q t nR O).exec inp s).out = s.out ∧
    (pA q t nR O).cost inp B s ≤
      (7 * ((parameters q t (s.regs nR)).r * (parameters q t (s.regs nR)).K + 1) + 4 * t + 40) *
        kappa B (RAM.bits M) := by
  sorry

end PartA

end EditMulticoloring.Dev.Ram
end
