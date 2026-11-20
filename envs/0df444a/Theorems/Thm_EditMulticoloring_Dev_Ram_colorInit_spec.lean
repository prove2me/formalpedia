-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_colorInit_spec
-- name    : EditMulticoloring.Dev.Ram.colorInit_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:32:42.641652+00:00
-- url     : https://prove2.me/theorems/edc170d6-e69c-4b3b-8ad0-ba771146ac75
-- title:
--   EditMulticoloring.Dev.Ram.colorInit_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem colorInit_spec {q : ℕ} (s : ℕ) (cfg : EnumCfg) (g XA DG : ℕ) (x : Word q) (st : HS)
--       (p W Q K Ms Mb : ℕ)
--       (hr0 : g + 51 ≤ cfg.r0) (hXA : XA < cfg.a0) (hDG : DG < cfg.a0) (hXD : XA ≠ DG)
--       (h0 : st.regs g = p) (h3 : st.regs (g + 3) = W) (h18 : st.regs (g + 18) = K)
--       (h24 : st.regs (g + 24) = Q)
--       (hlen : st.regs (cfg.lenR s) = x.length) (hx : WordAt st (cfg.buf s) 0 x)
--       (hp : p ≠ 0) (hpW : p < 2 ^ W)
--       (hMs : p * 2 ^ (2 * W) + 4 * 2 ^ (2 * W) ≤ Ms)
--       (hMb : q ^ x.length + 2 * q + cfg.a0 + s + XA + DG + 2 * x.length + Q + K + 2 ≤ Mb) :
--       let st' := (colorInit q s cfg g XA DG).exec inp st
--       GFCtx st' g p W ∧ st'.regs (g + 18) = K ∧ st'.regs (g + 24) = Q ∧
--       st'.regs (g + 25) = x.length ∧ WordAt st' XA 0 x ∧
--       (∀ i < K, st'.arr DG i = (value x / Q ^ i) % Q) ∧
--       (∀ r, (r < g ∨ g + 51 ≤ r) → st'.regs r = st.regs r) ∧
--       (∀ y i, y ≠ XA → y ≠ DG → st'.arr y i = st.arr y i) ∧
--       st'.cur = st.cur ∧ st'.out = st.out ∧
--       (colorInit q s cfg g XA DG).cost inp B st ≤
--         (16 * W + 12) * kappa B (RAM.bits Ms) + (14 * x.length + 7 * K + 26) * kappa B (RAM.bits Mb)
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.EnumCfg`, `EditMulticoloring.Dev.Ram.GFCtx`, `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.WordAt`, `EditMulticoloring.Dev.Ram.colorInit`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec`, `EditMulticoloring.Dev.Ram.EnumCfg.buf`, `EditMulticoloring.Dev.Ram.EnumCfg.lenR` and `EditMulticoloring.Dev.Ram.HS.arr` (definitions bundle `EMRamB000` of this split).
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

section Init
variable (inp : ℕ → ℕ) (B : ℕ)

theorem colorInit_spec {q : ℕ} (s : ℕ) (cfg : EnumCfg) (g XA DG : ℕ) (x : Word q) (st : HS)
    (p W Q K Ms Mb : ℕ)
    (hr0 : g + 51 ≤ cfg.r0) (hXA : XA < cfg.a0) (hDG : DG < cfg.a0) (hXD : XA ≠ DG)
    (h0 : st.regs g = p) (h3 : st.regs (g + 3) = W) (h18 : st.regs (g + 18) = K)
    (h24 : st.regs (g + 24) = Q)
    (hlen : st.regs (cfg.lenR s) = x.length) (hx : WordAt st (cfg.buf s) 0 x)
    (hp : p ≠ 0) (hpW : p < 2 ^ W)
    (hMs : p * 2 ^ (2 * W) + 4 * 2 ^ (2 * W) ≤ Ms)
    (hMb : q ^ x.length + 2 * q + cfg.a0 + s + XA + DG + 2 * x.length + Q + K + 2 ≤ Mb) :
    let st' := (colorInit q s cfg g XA DG).exec inp st
    GFCtx st' g p W ∧ st'.regs (g + 18) = K ∧ st'.regs (g + 24) = Q ∧
    st'.regs (g + 25) = x.length ∧ WordAt st' XA 0 x ∧
    (∀ i < K, st'.arr DG i = (value x / Q ^ i) % Q) ∧
    (∀ r, (r < g ∨ g + 51 ≤ r) → st'.regs r = st.regs r) ∧
    (∀ y i, y ≠ XA → y ≠ DG → st'.arr y i = st.arr y i) ∧
    st'.cur = st.cur ∧ st'.out = st.out ∧
    (colorInit q s cfg g XA DG).cost inp B st ≤
      (16 * W + 12) * kappa B (RAM.bits Ms) + (14 * x.length + 7 * K + 26) * kappa B (RAM.bits Mb) := by
  sorry

end Init

end EditMulticoloring.Dev.Ram
end
