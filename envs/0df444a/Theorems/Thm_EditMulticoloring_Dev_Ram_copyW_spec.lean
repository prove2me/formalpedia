-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_copyW_spec
-- name    : EditMulticoloring.Dev.Ram.copyW_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:33:10.558174+00:00
-- url     : https://prove2.me/theorems/0f1cf448-1f5b-455c-a8b5-754f72674d72
-- title:
--   EditMulticoloring.Dev.Ram.copyW_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem copyW_spec (S so D dO n j t u one : ℕ) (s : HS)
--       (hreg : [S, so, D, dO, n, j, t, u, one].Nodup)
--       (hSD : s.regs S ≠ s.regs D) (V M : ℕ)
--       (hV : ∀ i < s.regs n, s.arr (s.regs S) (s.regs so + i) ≤ V)
--       (hM : s.regs S + s.regs so + s.regs D + s.regs dO + s.regs n + V ≤ M) :
--       (∀ i < s.regs n, ((copyW S so D dO n j t u one).exec inp s).arr (s.regs D) (s.regs dO + i) =
--           s.arr (s.regs S) (s.regs so + i)) ∧
--       (∀ y i, ¬ (y = s.regs D ∧ s.regs dO ≤ i ∧ i < s.regs dO + s.regs n) →
--           ((copyW S so D dO n j t u one).exec inp s).arr y i = s.arr y i) ∧
--       (∀ r, r ≠ j → r ≠ t → r ≠ u → r ≠ one →
--           ((copyW S so D dO n j t u one).exec inp s).regs r = s.regs r) ∧
--       ((copyW S so D dO n j t u one).exec inp s).cur = s.cur ∧
--       ((copyW S so D dO n j t u one).exec inp s).out = s.out ∧
--       (copyW S so D dO n j t u one).cost inp B s ≤ (7 * s.regs n + 3) * kappa B (RAM.bits M)
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.copyW`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec` and `EditMulticoloring.Dev.Ram.HS.arr` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proofs of `EditMulticoloring.Dev.Ram.EnumCfg.delC_spec`, `EditMulticoloring.Dev.Ram.EnumCfg.insPhase`, `EditMulticoloring.Dev.Ram.EnumCfg.repPhase`, `EditMulticoloring.Dev.Ram.EnumCfg.visitC_spec`, `EditMulticoloring.Dev.Ram.cBody_spec`, `EditMulticoloring.Dev.Ram.colorInit_spec`, `EditMulticoloring.Dev.Ram.colorsAll_spec`, `EditMulticoloring.Dev.Ram.copyW_word`, `EditMulticoloring.Dev.Ram.encB_spec`, `EditMulticoloring.Dev.Ram.pC5_spec` and `EditMulticoloring.Dev.Ram.pC8_spec` of this split import it.
-- source:
--   the submitter, written with Claude, RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds; after the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819)

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000

section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section Copy
variable (inp : ℕ → ℕ) (B : ℕ)

theorem copyW_spec (S so D dO n j t u one : ℕ) (s : HS)
    (hreg : [S, so, D, dO, n, j, t, u, one].Nodup)
    (hSD : s.regs S ≠ s.regs D) (V M : ℕ)
    (hV : ∀ i < s.regs n, s.arr (s.regs S) (s.regs so + i) ≤ V)
    (hM : s.regs S + s.regs so + s.regs D + s.regs dO + s.regs n + V ≤ M) :
    (∀ i < s.regs n, ((copyW S so D dO n j t u one).exec inp s).arr (s.regs D) (s.regs dO + i) =
        s.arr (s.regs S) (s.regs so + i)) ∧
    (∀ y i, ¬ (y = s.regs D ∧ s.regs dO ≤ i ∧ i < s.regs dO + s.regs n) →
        ((copyW S so D dO n j t u one).exec inp s).arr y i = s.arr y i) ∧
    (∀ r, r ≠ j → r ≠ t → r ≠ u → r ≠ one →
        ((copyW S so D dO n j t u one).exec inp s).regs r = s.regs r) ∧
    ((copyW S so D dO n j t u one).exec inp s).cur = s.cur ∧
    ((copyW S so D dO n j t u one).exec inp s).out = s.out ∧
    (copyW S so D dO n j t u one).cost inp B s ≤ (7 * s.regs n + 3) * kappa B (RAM.bits M) := by
  sorry

end Copy

end EditMulticoloring.Dev.Ram
end
