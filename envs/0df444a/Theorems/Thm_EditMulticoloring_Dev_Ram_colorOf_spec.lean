-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_colorOf_spec
-- name    : EditMulticoloring.Dev.Ram.colorOf_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:32:28.114538+00:00
-- url     : https://prove2.me/theorems/284603ea-88a3-45a0-8a51-96448b31cef1
-- title:
--   EditMulticoloring.Dev.Ram.colorOf_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem colorOf_spec {q : ℕ} (t : ℕ) (cfg : EnumCfg) (g XA DG : ℕ) (x : Word q) (st : HS)
--       (p W Q K Vb Ms Mb : ℕ)
--       (hr0 : g + 51 ≤ cfg.r0) (hXA : XA < cfg.a0) (hDG : DG < cfg.a0) (hXD : XA ≠ DG)
--       (h0 : st.regs g = p) (h3 : st.regs (g + 3) = W) (h18 : st.regs (g + 18) = K)
--       (h24 : st.regs (g + 24) = Q)
--       (hlen : st.regs (cfg.lenR (2 * t)) = x.length) (hx : WordAt st (cfg.buf (2 * t)) 0 x)
--       (hp : p ≠ 0) (hpW : p < 2 ^ W) (hQ0 : 0 < Q) (hQW : Q ≤ 2 ^ W)
--       (hV : (visits (2 * t) x).length ≤ Vb)
--       (hMs : p * 2 ^ (2 * W) + 6 * 2 ^ (2 * W) + DG + (Vb + 2) * K + Vb ≤ Ms)
--       (hMb : q ^ x.length + 2 * q + cfg.a0 + 2 * t + XA + DG + 2 * x.length + Q + (Vb + 1) * K + Vb + 2
--         ≤ Mb) :
--       let st' := (colorOf q t cfg g XA DG).exec inp st
--       (∀ P : Parameters, P.Q = Q → P.K = K → st'.regs (g + 36) = localColor t P p x) ∧
--       (∀ r, (r < g + 1 ∨ r = g + 3 ∨ r = g + 18 ∨ r = g + 24 ∨ g + 51 ≤ r) →
--         ¬ cfg.ownsReg (2 * t) r → st'.regs r = st.regs r) ∧
--       (∀ y i, y ≠ XA → y ≠ DG → ¬ cfg.ownsArr (2 * t) y → st'.arr y i = st.arr y i) ∧
--       st'.regs (cfg.lenR (2 * t)) = x.length ∧ WordAt st' (cfg.buf (2 * t)) 0 x ∧
--       st'.cur = st.cur ∧ st'.out = st.out ∧
--       (colorOf q t cfg g XA DG).cost inp B st ≤
--         (Vb + 1) * ((19 * x.length + 7 * K + 40) * kappa B (RAM.bits Mb) +
--           cfg.enumE B q x.length (2 * t)) +
--         ((Q + 1) * (Vb + 1) * (K * (36 * W + 24) + 15) + 16 * W + 3 * Q + 18) * kappa B (RAM.bits Ms)
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.EnumCfg`, `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.WordAt`, `EditMulticoloring.Dev.Ram.colorOf`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.visits`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec`, `EditMulticoloring.Dev.Ram.EnumCfg.buf`, `EditMulticoloring.Dev.Ram.EnumCfg.enumE`, `EditMulticoloring.Dev.Ram.EnumCfg.lenR`, `EditMulticoloring.Dev.Ram.EnumCfg.ownsArr`, `EditMulticoloring.Dev.Ram.EnumCfg.ownsReg` and `EditMulticoloring.Dev.Ram.HS.arr` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proofs of `EditMulticoloring.Dev.Ram.cBody_spec` and `EditMulticoloring.Dev.Ram.colorsAll_spec` of this split import it.
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

theorem colorOf_spec {q : ℕ} (t : ℕ) (cfg : EnumCfg) (g XA DG : ℕ) (x : Word q) (st : HS)
    (p W Q K Vb Ms Mb : ℕ)
    (hr0 : g + 51 ≤ cfg.r0) (hXA : XA < cfg.a0) (hDG : DG < cfg.a0) (hXD : XA ≠ DG)
    (h0 : st.regs g = p) (h3 : st.regs (g + 3) = W) (h18 : st.regs (g + 18) = K)
    (h24 : st.regs (g + 24) = Q)
    (hlen : st.regs (cfg.lenR (2 * t)) = x.length) (hx : WordAt st (cfg.buf (2 * t)) 0 x)
    (hp : p ≠ 0) (hpW : p < 2 ^ W) (hQ0 : 0 < Q) (hQW : Q ≤ 2 ^ W)
    (hV : (visits (2 * t) x).length ≤ Vb)
    (hMs : p * 2 ^ (2 * W) + 6 * 2 ^ (2 * W) + DG + (Vb + 2) * K + Vb ≤ Ms)
    (hMb : q ^ x.length + 2 * q + cfg.a0 + 2 * t + XA + DG + 2 * x.length + Q + (Vb + 1) * K + Vb + 2
      ≤ Mb) :
    let st' := (colorOf q t cfg g XA DG).exec inp st
    (∀ P : Parameters, P.Q = Q → P.K = K → st'.regs (g + 36) = localColor t P p x) ∧
    (∀ r, (r < g + 1 ∨ r = g + 3 ∨ r = g + 18 ∨ r = g + 24 ∨ g + 51 ≤ r) →
      ¬ cfg.ownsReg (2 * t) r → st'.regs r = st.regs r) ∧
    (∀ y i, y ≠ XA → y ≠ DG → ¬ cfg.ownsArr (2 * t) y → st'.arr y i = st.arr y i) ∧
    st'.regs (cfg.lenR (2 * t)) = x.length ∧ WordAt st' (cfg.buf (2 * t)) 0 x ∧
    st'.cur = st.cur ∧ st'.out = st.out ∧
    (colorOf q t cfg g XA DG).cost inp B st ≤
      (Vb + 1) * ((19 * x.length + 7 * K + 40) * kappa B (RAM.bits Mb) +
        cfg.enumE B q x.length (2 * t)) +
      ((Q + 1) * (Vb + 1) * (K * (36 * W + 24) + 15) + 16 * W + 3 * Q + 18) * kappa B (RAM.bits Ms) := by
  sorry

end Out

end EditMulticoloring.Dev.Ram
end
