-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_encF_spec
-- name    : EditMulticoloring.Dev.Ram.encF_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:33:17.564089+00:00
-- url     : https://prove2.me/theorems/992a6b77-1547-4bad-82bc-469b6a53cbf2
-- title:
--   EditMulticoloring.Dev.Ram.encF_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem encF_spec (q t n p : ℕ) (hq : 2 ≤ q) (s : HS) (hs : EBase q t n p s) :
--       let s' := (encF q t).exec inp s
--       let T := shortTable q t (parameters q t n).h
--       EBase q t n p s' ∧ (∀ r, r < 310 + 12 * t → s'.regs r = s.regs r) ∧
--       (∀ y i, y < 14 + 4 * t → s'.arr y i = s.arr y i) ∧
--       (∀ i (hi : i < T.length), Code.repr q (parameters q t n).ρ (s'.arr (14 + 4 * t) i) = T[i]) ∧
--       (∀ i, i < T.length → s'.arr (14 + 4 * t) i < q ^ (parameters q t n).ρ) ∧
--       T.length = min (q ^ (parameters q t n).h) (s'.regs (312 + 12 * t)) ∧
--       (∀ z ∈ T, z.length = (parameters q t n).ρ) ∧ s'.regs (312 + 12 * t) ≤ q ^ (parameters q t n).ρ ∧
--       s'.cur = s.cur ∧ s'.out = s.out ∧
--       (encF q t).cost inp B s ≤ 2 * kappa B (RAM.bits (encM q t n)) +
--         EncS.shortCost B q t (parameters q t n).ρ (14 + 4 * t)
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.EBase`, `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.encF`, `EditMulticoloring.Dev.Ram.encM`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec`, `EditMulticoloring.Dev.Ram.EncS.shortCost` and `EditMulticoloring.Dev.Ram.HS.arr` (definitions bundle `EMRamB000` of this split).
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

section Phases
variable (inp : ℕ → ℕ) (B : ℕ)

theorem encF_spec (q t n p : ℕ) (hq : 2 ≤ q) (s : HS) (hs : EBase q t n p s) :
    let s' := (encF q t).exec inp s
    let T := shortTable q t (parameters q t n).h
    EBase q t n p s' ∧ (∀ r, r < 310 + 12 * t → s'.regs r = s.regs r) ∧
    (∀ y i, y < 14 + 4 * t → s'.arr y i = s.arr y i) ∧
    (∀ i (hi : i < T.length), Code.repr q (parameters q t n).ρ (s'.arr (14 + 4 * t) i) = T[i]) ∧
    (∀ i, i < T.length → s'.arr (14 + 4 * t) i < q ^ (parameters q t n).ρ) ∧
    T.length = min (q ^ (parameters q t n).h) (s'.regs (312 + 12 * t)) ∧
    (∀ z ∈ T, z.length = (parameters q t n).ρ) ∧ s'.regs (312 + 12 * t) ≤ q ^ (parameters q t n).ρ ∧
    s'.cur = s.cur ∧ s'.out = s.out ∧
    (encF q t).cost inp B s ≤ 2 * kappa B (RAM.bits (encM q t n)) +
      EncS.shortCost B q t (parameters q t n).ρ (14 + 4 * t) := by
  sorry

end Phases

end EditMulticoloring.Dev.Ram
end
