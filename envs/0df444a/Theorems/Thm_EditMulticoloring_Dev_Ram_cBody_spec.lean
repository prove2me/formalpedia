-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_cBody_spec
-- name    : EditMulticoloring.Dev.Ram.cBody_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:32:28.349584+00:00
-- url     : https://prove2.me/theorems/6eebb3c7-48c6-416f-accd-e1af17a6882c
-- title:
--   EditMulticoloring.Dev.Ram.cBody_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem cBody_spec {q : ℕ} (t : ℕ) (cfg1 cfg2 : EnumCfg) (g X2 XA DG CLA : ℕ) (x : Word q) (st0 : HS)
--       (p W Q K Vb Ms Mb : ℕ) (hpl : CAPlace t cfg1 cfg2 g X2 XA DG CLA)
--       (e0 : st0.regs g = p) (e3 : st0.regs (g + 3) = W) (e18 : st0.regs (g + 18) = K)
--       (e24 : st0.regs (g + 24) = Q) (e53 : st0.regs (g + 53) = x.length) (hX0 : WordAt st0 X2 0 x)
--       (hp : p ≠ 0) (hpW : p < 2 ^ W) (hQ0 : 0 < Q) (hQW : Q ≤ 2 ^ W)
--       (hVb : visBound q t x.length ≤ Vb)
--       (hMs : p * 2 ^ (2 * W) + 6 * 2 ^ (2 * W) + DG + (Vb + 2) * K + Vb ≤ Ms)
--       (hMb : q ^ x.length + 2 * q + 2 * cfg1.a0 + 2 * t + X2 + XA + DG + CLA + 2 * x.length + Q +
--         (Vb + 1) * K + Vb + 2 * 2 ^ (2 * W) + 2 ≤ Mb)
--       (l : List (Word q)) (st : HS) (w : Word q) (hI : CAInv t cfg1 cfg2 g XA DG CLA p Q K x st0 l st)
--       (hVL : st.regs cfg1.VL = w.length) (hvis : WordAt st cfg1.vis 0 w)
--       (hwl : w.length ≤ x.length + 2 * t) (hJ : l.length ≤ Vb) :
--       CAInv t cfg1 cfg2 g XA DG CLA p Q K x st0 (listF x l w)
--         ((cBody q t cfg1 cfg2 g X2 XA DG CLA).exec inp st) ∧
--       cfg1.BodyFrame (2 * t) st ((cBody q t cfg1 cfg2 g X2 XA DG CLA).exec inp st) ∧
--       (cBody q t cfg1 cfg2 g X2 XA DG CLA).cost inp B st ≤
--         colorOfCost B q t x.length K Q W Vb Ms Mb cfg2 + (19 * x.length + 40) * kappa B (RAM.bits Mb)
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.CAInv`, `EditMulticoloring.Dev.Ram.CAPlace`, `EditMulticoloring.Dev.Ram.EnumCfg`, `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.WordAt`, `EditMulticoloring.Dev.Ram.cBody`, `EditMulticoloring.Dev.Ram.colorOfCost`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.listF`, `EditMulticoloring.Dev.Ram.visBound`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec`, `EditMulticoloring.Dev.Ram.EnumCfg.BodyFrame`, `EditMulticoloring.Dev.Ram.EnumCfg.VL` and `EditMulticoloring.Dev.Ram.EnumCfg.vis` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proof of `EditMulticoloring.Dev.Ram.colorsAll_spec` of this split imports it.
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
theorem cBody_spec {q : ℕ} (t : ℕ) (cfg1 cfg2 : EnumCfg) (g X2 XA DG CLA : ℕ) (x : Word q) (st0 : HS)
    (p W Q K Vb Ms Mb : ℕ) (hpl : CAPlace t cfg1 cfg2 g X2 XA DG CLA)
    (e0 : st0.regs g = p) (e3 : st0.regs (g + 3) = W) (e18 : st0.regs (g + 18) = K)
    (e24 : st0.regs (g + 24) = Q) (e53 : st0.regs (g + 53) = x.length) (hX0 : WordAt st0 X2 0 x)
    (hp : p ≠ 0) (hpW : p < 2 ^ W) (hQ0 : 0 < Q) (hQW : Q ≤ 2 ^ W)
    (hVb : visBound q t x.length ≤ Vb)
    (hMs : p * 2 ^ (2 * W) + 6 * 2 ^ (2 * W) + DG + (Vb + 2) * K + Vb ≤ Ms)
    (hMb : q ^ x.length + 2 * q + 2 * cfg1.a0 + 2 * t + X2 + XA + DG + CLA + 2 * x.length + Q +
      (Vb + 1) * K + Vb + 2 * 2 ^ (2 * W) + 2 ≤ Mb)
    (l : List (Word q)) (st : HS) (w : Word q) (hI : CAInv t cfg1 cfg2 g XA DG CLA p Q K x st0 l st)
    (hVL : st.regs cfg1.VL = w.length) (hvis : WordAt st cfg1.vis 0 w)
    (hwl : w.length ≤ x.length + 2 * t) (hJ : l.length ≤ Vb) :
    CAInv t cfg1 cfg2 g XA DG CLA p Q K x st0 (listF x l w)
      ((cBody q t cfg1 cfg2 g X2 XA DG CLA).exec inp st) ∧
    cfg1.BodyFrame (2 * t) st ((cBody q t cfg1 cfg2 g X2 XA DG CLA).exec inp st) ∧
    (cBody q t cfg1 cfg2 g X2 XA DG CLA).cost inp B st ≤
      colorOfCost B q t x.length K Q W Vb Ms Mb cfg2 + (19 * x.length + 40) * kappa B (RAM.bits Mb) := by
  sorry

end Body

end EditMulticoloring.Dev.Ram
end
