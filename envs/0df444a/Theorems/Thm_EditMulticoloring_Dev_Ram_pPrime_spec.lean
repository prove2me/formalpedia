-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_pPrime_spec
-- name    : EditMulticoloring.Dev.Ram.pPrime_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:35:21.91646+00:00
-- url     : https://prove2.me/theorems/99a2b2f2-771d-4860-bb81-249a7dc6a62a
-- title:
--   EditMulticoloring.Dev.Ram.pPrime_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem pPrime_spec (q PR O : ℕ) (s : HS) (M : ℕ) (hq : 2 ≤ q) (hPR : PR < O)
--       (hM : (primeBound (s.regs (O + 5)) + 2) * (q + 1) + s.regs PR +
--         3 * primeBound (s.regs (O + 5)) + s.regs (O + 9) + 10 ≤ M) :
--       ((pPrime q PR O).exec inp s).regs (O + 10) = ceilLog q (primeAt (s.regs (O + 5) - 1)) ∧
--       ((pPrime q PR O).exec inp s).regs (O + 11) =
--         s.regs (O + 9) + ceilLog q (primeAt (s.regs (O + 5) - 1)) ∧
--       (∀ i ≤ s.regs (O + 5), ((pPrime q PR O).exec inp s).arr (s.regs PR) i = primeAt i) ∧
--       (∀ y i, ¬ (y = s.regs PR ∧ i < Nat.count Nat.Prime (primeBound (s.regs (O + 5)))) →
--         ((pPrime q PR O).exec inp s).arr y i = s.arr y i) ∧
--       (∀ r', (r' < O + 10 ∨ (O + 12 ≤ r' ∧ r' < O + 17) ∨ O + 49 ≤ r') →
--         ((pPrime q PR O).exec inp s).regs r' = s.regs r') ∧
--       ((pPrime q PR O).exec inp s).cur = s.cur ∧
--       ((pPrime q PR O).exec inp s).out = s.out ∧
--       (pPrime q PR O).cost inp B s ≤
--         ((8 * primeBound (s.regs (O + 5)) + 13) * (primeBound (s.regs (O + 5)) + 1) +
--           14 * primeBound (s.regs (O + 5)) + 40) * kappa B (RAM.bits M)
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.pPrime`, `EditMulticoloring.Dev.Ram.primeBound`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec` and `EditMulticoloring.Dev.Ram.HS.arr` (definitions bundle `EMRamB000` of this split).
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

section PartP
variable (inp : ℕ → ℕ) (B : ℕ)

theorem pPrime_spec (q PR O : ℕ) (s : HS) (M : ℕ) (hq : 2 ≤ q) (hPR : PR < O)
    (hM : (primeBound (s.regs (O + 5)) + 2) * (q + 1) + s.regs PR +
      3 * primeBound (s.regs (O + 5)) + s.regs (O + 9) + 10 ≤ M) :
    ((pPrime q PR O).exec inp s).regs (O + 10) = ceilLog q (primeAt (s.regs (O + 5) - 1)) ∧
    ((pPrime q PR O).exec inp s).regs (O + 11) =
      s.regs (O + 9) + ceilLog q (primeAt (s.regs (O + 5) - 1)) ∧
    (∀ i ≤ s.regs (O + 5), ((pPrime q PR O).exec inp s).arr (s.regs PR) i = primeAt i) ∧
    (∀ y i, ¬ (y = s.regs PR ∧ i < Nat.count Nat.Prime (primeBound (s.regs (O + 5)))) →
      ((pPrime q PR O).exec inp s).arr y i = s.arr y i) ∧
    (∀ r', (r' < O + 10 ∨ (O + 12 ≤ r' ∧ r' < O + 17) ∨ O + 49 ≤ r') →
      ((pPrime q PR O).exec inp s).regs r' = s.regs r') ∧
    ((pPrime q PR O).exec inp s).cur = s.cur ∧
    ((pPrime q PR O).exec inp s).out = s.out ∧
    (pPrime q PR O).cost inp B s ≤
      ((8 * primeBound (s.regs (O + 5)) + 13) * (primeBound (s.regs (O + 5)) + 1) +
        14 * primeBound (s.regs (O + 5)) + 40) * kappa B (RAM.bits M) := by
  sorry

end PartP

end EditMulticoloring.Dev.Ram
end
