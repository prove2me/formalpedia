-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_colorsAll_spec
-- name    : EditMulticoloring.Dev.Ram.colorsAll_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:33:00.008291+00:00
-- url     : https://prove2.me/theorems/7023e4e2-7306-4e14-b65f-e6a2b723cb8e
-- title:
--   EditMulticoloring.Dev.Ram.colorsAll_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem colorsAll_spec {q : ℕ} (t : ℕ) (cfg1 cfg2 : EnumCfg) (g X2 XA DG CLA : ℕ) (x : Word q)
--       (st : HS) (p W Q K Vb Ms Mb : ℕ) (hpl : CAPlace t cfg1 cfg2 g X2 XA DG CLA)
--       (h0 : st.regs g = p) (h3 : st.regs (g + 3) = W) (h18 : st.regs (g + 18) = K)
--       (h24 : st.regs (g + 24) = Q)
--       (hlen : st.regs (cfg1.lenR (2 * t)) = x.length) (hx : WordAt st (cfg1.buf (2 * t)) 0 x)
--       (hp : p ≠ 0) (hpW : p < 2 ^ W) (hQ0 : 0 < Q) (hQW : Q ≤ 2 ^ W)
--       (hVb : visBound q t x.length ≤ Vb)
--       (hMs : p * 2 ^ (2 * W) + 6 * 2 ^ (2 * W) + DG + (Vb + 2) * K + Vb ≤ Ms)
--       (hMb : q ^ x.length + 2 * q + 2 * cfg1.a0 + 2 * t + X2 + XA + DG + CLA + 2 * x.length + Q +
--         (Vb + 1) * K + Vb + 2 * 2 ^ (2 * W) + 2 ≤ Mb) :
--       let st' := (colorsAll q t cfg1 cfg2 g X2 XA DG CLA).exec inp st
--       (∀ P : Parameters, P.Q = Q → P.K = K → st'.regs (g + 51) = localColor t P p x) ∧
--       st'.regs (g + 52) = (nbrList t x).length ∧
--       (∀ m (hm : m < (nbrList t x).length), ∀ P : Parameters, P.Q = Q → P.K = K →
--         st'.arr CLA m = localColor t P p (nbrList t x)[m]) ∧
--       (∀ r, (r < g + 1 ∨ r = g + 3 ∨ r = g + 18 ∨ r = g + 24 ∨ cfg1.r0 ≤ r) →
--         ¬ cfg1.ownsReg (2 * t) r → st'.regs r = st.regs r) ∧
--       (∀ y i, y ≠ X2 → y ≠ XA → y ≠ DG → y ≠ CLA → ¬ cfg2.ownsArr (2 * t) y →
--         ¬ cfg1.ownsArr (2 * t) y → st'.arr y i = st.arr y i) ∧
--       st'.regs (cfg1.lenR (2 * t)) = x.length ∧ WordAt st' (cfg1.buf (2 * t)) 0 x ∧
--       st'.cur = st.cur ∧ st'.out = st.out ∧
--       (colorsAll q t cfg1 cfg2 g X2 XA DG CLA).cost inp B st ≤
--         (Vb + 1) * (colorOfCost B q t x.length K Q W Vb Ms Mb cfg2 +
--           (19 * x.length + 40) * kappa B (RAM.bits Mb) + cfg1.enumE B q x.length (2 * t))
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.CAPlace`, `EditMulticoloring.Dev.Ram.EnumCfg`, `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.WordAt`, `EditMulticoloring.Dev.Ram.colorOfCost`, `EditMulticoloring.Dev.Ram.colorsAll`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.nbrList`, `EditMulticoloring.Dev.Ram.visBound`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec`, `EditMulticoloring.Dev.Ram.EnumCfg.buf`, `EditMulticoloring.Dev.Ram.EnumCfg.enumE`, `EditMulticoloring.Dev.Ram.EnumCfg.lenR`, `EditMulticoloring.Dev.Ram.EnumCfg.ownsArr`, `EditMulticoloring.Dev.Ram.EnumCfg.ownsReg` and `EditMulticoloring.Dev.Ram.HS.arr` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proofs of `EditMulticoloring.Dev.Ram.encProg_spec` and `EditMulticoloring.Dev.Ram.pC5_spec` of this split import it.
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

section Body
variable (inp : ℕ → ℕ) (B : ℕ)

set_option maxHeartbeats 1600000 in
theorem colorsAll_spec {q : ℕ} (t : ℕ) (cfg1 cfg2 : EnumCfg) (g X2 XA DG CLA : ℕ) (x : Word q)
    (st : HS) (p W Q K Vb Ms Mb : ℕ) (hpl : CAPlace t cfg1 cfg2 g X2 XA DG CLA)
    (h0 : st.regs g = p) (h3 : st.regs (g + 3) = W) (h18 : st.regs (g + 18) = K)
    (h24 : st.regs (g + 24) = Q)
    (hlen : st.regs (cfg1.lenR (2 * t)) = x.length) (hx : WordAt st (cfg1.buf (2 * t)) 0 x)
    (hp : p ≠ 0) (hpW : p < 2 ^ W) (hQ0 : 0 < Q) (hQW : Q ≤ 2 ^ W)
    (hVb : visBound q t x.length ≤ Vb)
    (hMs : p * 2 ^ (2 * W) + 6 * 2 ^ (2 * W) + DG + (Vb + 2) * K + Vb ≤ Ms)
    (hMb : q ^ x.length + 2 * q + 2 * cfg1.a0 + 2 * t + X2 + XA + DG + CLA + 2 * x.length + Q +
      (Vb + 1) * K + Vb + 2 * 2 ^ (2 * W) + 2 ≤ Mb) :
    let st' := (colorsAll q t cfg1 cfg2 g X2 XA DG CLA).exec inp st
    (∀ P : Parameters, P.Q = Q → P.K = K → st'.regs (g + 51) = localColor t P p x) ∧
    st'.regs (g + 52) = (nbrList t x).length ∧
    (∀ m (hm : m < (nbrList t x).length), ∀ P : Parameters, P.Q = Q → P.K = K →
      st'.arr CLA m = localColor t P p (nbrList t x)[m]) ∧
    (∀ r, (r < g + 1 ∨ r = g + 3 ∨ r = g + 18 ∨ r = g + 24 ∨ cfg1.r0 ≤ r) →
      ¬ cfg1.ownsReg (2 * t) r → st'.regs r = st.regs r) ∧
    (∀ y i, y ≠ X2 → y ≠ XA → y ≠ DG → y ≠ CLA → ¬ cfg2.ownsArr (2 * t) y →
      ¬ cfg1.ownsArr (2 * t) y → st'.arr y i = st.arr y i) ∧
    st'.regs (cfg1.lenR (2 * t)) = x.length ∧ WordAt st' (cfg1.buf (2 * t)) 0 x ∧
    st'.cur = st.cur ∧ st'.out = st.out ∧
    (colorsAll q t cfg1 cfg2 g X2 XA DG CLA).cost inp B st ≤
      (Vb + 1) * (colorOfCost B q t x.length K Q W Vb Ms Mb cfg2 +
        (19 * x.length + 40) * kappa B (RAM.bits Mb) + cfg1.enumE B q x.length (2 * t)) := by
  sorry

end Body

end EditMulticoloring.Dev.Ram
end
