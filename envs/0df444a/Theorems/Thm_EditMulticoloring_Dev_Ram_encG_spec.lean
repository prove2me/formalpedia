-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_encG_spec
-- name    : EditMulticoloring.Dev.Ram.encG_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:33:39.378357+00:00
-- url     : https://prove2.me/theorems/3fece319-bc66-42c4-82cb-c900c3ff2972
-- title:
--   EditMulticoloring.Dev.Ram.encG_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem encG_spec (q t n p : ℕ) (hq : 2 ≤ q) (s : HS) (hs : EBase q t n p s) (w : Word q)
--       (hw : WordAt s 2 0 w) (hmk : (parameters q t n).m ≤ w.length) (hout : s.out = [])
--       (hidx : s.regs 22 < q ^ (parameters q t n).h) (hcnt : s.regs (312 + 12 * t) ≤ q ^ (parameters q t n).ρ)
--       (hT : s.regs 22 < min (q ^ (parameters q t n).h) (s.regs (312 + 12 * t)) →
--         s.arr (14 + 4 * t) (s.regs 22) < q ^ (parameters q t n).ρ) :
--       let s' := (encG q t).exec inp s
--       s'.out = (w.take (parameters q t n).m).map (fun a => a.val) ++
--         (if s.regs 22 < min (q ^ (parameters q t n).h) (s.regs (312 + 12 * t)) then
--           (Code.repr q (parameters q t n).ρ (s.arr (14 + 4 * t) (s.regs 22))).map (fun a => a.val) else []) ∧
--       s'.regs 30 = 1 ∧
--       (encG q t).cost inp B s ≤ (6 * (parameters q t n).m + 13 * (parameters q t n).ρ + 30) *
--         kappa B (RAM.bits (encM q t n))
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.EBase`, `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.WordAt`, `EditMulticoloring.Dev.Ram.encG`, `EditMulticoloring.Dev.Ram.encM`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec` and `EditMulticoloring.Dev.Ram.HS.arr` (definitions bundle `EMRamB000` of this split).
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

theorem encG_spec (q t n p : ℕ) (hq : 2 ≤ q) (s : HS) (hs : EBase q t n p s) (w : Word q)
    (hw : WordAt s 2 0 w) (hmk : (parameters q t n).m ≤ w.length) (hout : s.out = [])
    (hidx : s.regs 22 < q ^ (parameters q t n).h) (hcnt : s.regs (312 + 12 * t) ≤ q ^ (parameters q t n).ρ)
    (hT : s.regs 22 < min (q ^ (parameters q t n).h) (s.regs (312 + 12 * t)) →
      s.arr (14 + 4 * t) (s.regs 22) < q ^ (parameters q t n).ρ) :
    let s' := (encG q t).exec inp s
    s'.out = (w.take (parameters q t n).m).map (fun a => a.val) ++
      (if s.regs 22 < min (q ^ (parameters q t n).h) (s.regs (312 + 12 * t)) then
        (Code.repr q (parameters q t n).ρ (s.arr (14 + 4 * t) (s.regs 22))).map (fun a => a.val) else []) ∧
    s'.regs 30 = 1 ∧
    (encG q t).cost inp B s ≤ (6 * (parameters q t n).m + 13 * (parameters q t n).ρ + 30) *
      kappa B (RAM.bits (encM q t n)) := by
  sorry

end Phases

end EditMulticoloring.Dev.Ram
end
