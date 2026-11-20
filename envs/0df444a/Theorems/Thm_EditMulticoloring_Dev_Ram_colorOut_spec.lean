-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_colorOut_spec
-- name    : EditMulticoloring.Dev.Ram.colorOut_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:32:32.85645+00:00
-- url     : https://prove2.me/theorems/f26acaa0-6ba6-4a6b-80dc-23817d99b984
-- title:
--   EditMulticoloring.Dev.Ram.colorOut_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem colorOut_spec (g : ℕ) (s : HS) (p W Q K DG α id Ms : ℕ)
--       (hctx : GFCtx s g p W) (hp : p ≠ 0) (hpW : p < 2 ^ W) (hQ0 : 0 < Q) (hQW : Q ≤ 2 ^ W)
--       (h16 : s.regs (g + 16) = DG) (h18 : s.regs (g + 18) = K) (h24 : s.regs (g + 24) = Q)
--       (h27 : s.regs (g + 27) = α) (hα : α < Q)
--       (hrow : ∀ i < K, s.arr DG i = (id / Q ^ i) % Q)
--       (hMs : p * 2 ^ (2 * W) + 6 * 2 ^ (2 * W) + DG + 2 * K ≤ Ms) :
--       ((colorOut g).exec inp s).regs (g + 36) = Q * α + bitEval Q p K id α ∧
--       (∀ r, KeepS g r → ((colorOut g).exec inp s).regs r = s.regs r) ∧
--       ((colorOut g).exec inp s).mem = s.mem ∧
--       ((colorOut g).exec inp s).cur = s.cur ∧ ((colorOut g).exec inp s).out = s.out ∧
--       (colorOut g).cost inp B s ≤ (K * (36 * W + 24) + 8) * kappa B (RAM.bits Ms)
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.GFCtx`, `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.KeepS`, `EditMulticoloring.Dev.Ram.colorOut`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec` and `EditMulticoloring.Dev.Ram.HS.arr` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proof of `EditMulticoloring.Dev.Ram.colorOf_spec` of this split imports it.
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

section Out
variable (inp : ℕ → ℕ) (B : ℕ)

theorem colorOut_spec (g : ℕ) (s : HS) (p W Q K DG α id Ms : ℕ)
    (hctx : GFCtx s g p W) (hp : p ≠ 0) (hpW : p < 2 ^ W) (hQ0 : 0 < Q) (hQW : Q ≤ 2 ^ W)
    (h16 : s.regs (g + 16) = DG) (h18 : s.regs (g + 18) = K) (h24 : s.regs (g + 24) = Q)
    (h27 : s.regs (g + 27) = α) (hα : α < Q)
    (hrow : ∀ i < K, s.arr DG i = (id / Q ^ i) % Q)
    (hMs : p * 2 ^ (2 * W) + 6 * 2 ^ (2 * W) + DG + 2 * K ≤ Ms) :
    ((colorOut g).exec inp s).regs (g + 36) = Q * α + bitEval Q p K id α ∧
    (∀ r, KeepS g r → ((colorOut g).exec inp s).regs r = s.regs r) ∧
    ((colorOut g).exec inp s).mem = s.mem ∧
    ((colorOut g).exec inp s).cur = s.cur ∧ ((colorOut g).exec inp s).out = s.out ∧
    (colorOut g).cost inp B s ≤ (K * (36 * W + 24) + 8) * kappa B (RAM.bits Ms) := by
  sorry

end Out

end EditMulticoloring.Dev.Ram
end
