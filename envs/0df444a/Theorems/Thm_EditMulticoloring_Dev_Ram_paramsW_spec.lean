-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_paramsW_spec
-- name    : EditMulticoloring.Dev.Ram.paramsW_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:35:42.318775+00:00
-- url     : https://prove2.me/theorems/f6bb398c-d4f9-48fe-aacc-caabda5e0b33
-- title:
--   EditMulticoloring.Dev.Ram.paramsW_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem paramsW_spec (q t nR PR O : ℕ) (s : HS) (M : ℕ) (hq : 2 ≤ q) (hn : nR < O) (hPR : PR < O)
--       (hw : ∃ l ≤ s.regs nR, rhoCond q t (parameters q t (s.regs nR)).h l)
--       (hM : paramsBound q t (s.regs nR) (s.regs PR) ≤ M) :
--       ParamsAt ((paramsW q t nR PR O).exec inp s) O q t (s.regs nR) ∧
--       (∀ i ≤ (parameters q t (s.regs nR)).L,
--         ((paramsW q t nR PR O).exec inp s).arr (s.regs PR) i = primeAt i) ∧
--       (∀ y i, ¬ (y = s.regs PR ∧ i < Nat.count Nat.Prime (primeBound (parameters q t (s.regs nR)).L)) →
--         ((paramsW q t nR PR O).exec inp s).arr y i = s.arr y i) ∧
--       (∀ r', (r' < O ∨ O + 49 ≤ r') → ((paramsW q t nR PR O).exec inp s).regs r' = s.regs r') ∧
--       ((paramsW q t nR PR O).exec inp s).cur = s.cur ∧
--       ((paramsW q t nR PR O).exec inp s).out = s.out ∧
--       (paramsW q t nR PR O).cost inp B s ≤ paramsCost q t (s.regs nR) * kappa B (RAM.bits M)
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.ParamsAt`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.paramsBound`, `EditMulticoloring.Dev.Ram.paramsCost`, `EditMulticoloring.Dev.Ram.paramsW`, `EditMulticoloring.Dev.Ram.primeBound`, `EditMulticoloring.Dev.Ram.rhoCond`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec` and `EditMulticoloring.Dev.Ram.HS.arr` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proofs of `EditMulticoloring.Dev.Ram.decPre_spec` and `EditMulticoloring.Dev.Ram.encProg_spec` of this split import it.
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

section Params
variable (inp : ℕ → ℕ) (B : ℕ)

theorem paramsW_spec (q t nR PR O : ℕ) (s : HS) (M : ℕ) (hq : 2 ≤ q) (hn : nR < O) (hPR : PR < O)
    (hw : ∃ l ≤ s.regs nR, rhoCond q t (parameters q t (s.regs nR)).h l)
    (hM : paramsBound q t (s.regs nR) (s.regs PR) ≤ M) :
    ParamsAt ((paramsW q t nR PR O).exec inp s) O q t (s.regs nR) ∧
    (∀ i ≤ (parameters q t (s.regs nR)).L,
      ((paramsW q t nR PR O).exec inp s).arr (s.regs PR) i = primeAt i) ∧
    (∀ y i, ¬ (y = s.regs PR ∧ i < Nat.count Nat.Prime (primeBound (parameters q t (s.regs nR)).L)) →
      ((paramsW q t nR PR O).exec inp s).arr y i = s.arr y i) ∧
    (∀ r', (r' < O ∨ O + 49 ≤ r') → ((paramsW q t nR PR O).exec inp s).regs r' = s.regs r') ∧
    ((paramsW q t nR PR O).exec inp s).cur = s.cur ∧
    ((paramsW q t nR PR O).exec inp s).out = s.out ∧
    (paramsW q t nR PR O).cost inp B s ≤ paramsCost q t (s.regs nR) * kappa B (RAM.bits M) := by
  sorry

end Params

end EditMulticoloring.Dev.Ram
end
