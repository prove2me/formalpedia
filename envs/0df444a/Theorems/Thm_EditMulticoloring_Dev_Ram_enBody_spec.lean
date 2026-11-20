-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_enBody_spec
-- name    : EditMulticoloring.Dev.Ram.enBody_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:33:18.179968+00:00
-- url     : https://prove2.me/theorems/98cba2e5-ea9f-4958-b2a8-a7c874efdedc
-- title:
--   EditMulticoloring.Dev.Ram.enBody_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem enBody_spec {q : ℕ} (s : ℕ) (cfg : EnumCfg) (g XA DG K Q V Mb : ℕ) (x : Word q) (st0 : HS)
--       (hr0 : g + 51 ≤ cfg.r0) (hXA : XA < cfg.a0) (hDG : DG < cfg.a0) (hXD : XA ≠ DG)
--       (e18 : st0.regs (g + 18) = K) (e24 : st0.regs (g + 24) = Q) (e25 : st0.regs (g + 25) = x.length)
--       (hX0 : WordAt st0 XA 0 x)
--       (hMb : q ^ x.length + 2 * q + cfg.a0 + s + XA + DG + 2 * x.length + Q + (V + 1) * K + V + 2 ≤ Mb)
--       (l : List (Word q)) (st : HS) (w : Word q) (hI : EnInv s cfg g DG K Q x st0 l st)
--       (hVL : st.regs cfg.VL = w.length) (hvis : WordAt st cfg.vis 0 w)
--       (hwl : w.length ≤ x.length + s) (hJ : l.length + 1 ≤ V) :
--       EnInv s cfg g DG K Q x st0 (listF x l w) ((enBody q cfg g XA DG).exec inp st) ∧
--       cfg.BodyFrame s st ((enBody q cfg g XA DG).exec inp st) ∧
--       (enBody q cfg g XA DG).cost inp B st ≤ (19 * x.length + 7 * K + 40) * kappa B (RAM.bits Mb)
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.EnInv`, `EditMulticoloring.Dev.Ram.EnumCfg`, `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.WordAt`, `EditMulticoloring.Dev.Ram.enBody`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.listF`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec`, `EditMulticoloring.Dev.Ram.EnumCfg.BodyFrame`, `EditMulticoloring.Dev.Ram.EnumCfg.VL` and `EditMulticoloring.Dev.Ram.EnumCfg.vis` (definitions bundle `EMRamB000` of this split).
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

section Enum
variable (inp : ℕ → ℕ) (B : ℕ)

set_option maxHeartbeats 1600000 in
theorem enBody_spec {q : ℕ} (s : ℕ) (cfg : EnumCfg) (g XA DG K Q V Mb : ℕ) (x : Word q) (st0 : HS)
    (hr0 : g + 51 ≤ cfg.r0) (hXA : XA < cfg.a0) (hDG : DG < cfg.a0) (hXD : XA ≠ DG)
    (e18 : st0.regs (g + 18) = K) (e24 : st0.regs (g + 24) = Q) (e25 : st0.regs (g + 25) = x.length)
    (hX0 : WordAt st0 XA 0 x)
    (hMb : q ^ x.length + 2 * q + cfg.a0 + s + XA + DG + 2 * x.length + Q + (V + 1) * K + V + 2 ≤ Mb)
    (l : List (Word q)) (st : HS) (w : Word q) (hI : EnInv s cfg g DG K Q x st0 l st)
    (hVL : st.regs cfg.VL = w.length) (hvis : WordAt st cfg.vis 0 w)
    (hwl : w.length ≤ x.length + s) (hJ : l.length + 1 ≤ V) :
    EnInv s cfg g DG K Q x st0 (listF x l w) ((enBody q cfg g XA DG).exec inp st) ∧
    cfg.BodyFrame s st ((enBody q cfg g XA DG).exec inp st) ∧
    (enBody q cfg g XA DG).cost inp B st ≤ (19 * x.length + 7 * K + 40) * kappa B (RAM.bits Mb) := by
  sorry

end Enum

end EditMulticoloring.Dev.Ram
end
