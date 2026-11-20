-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_EncS_markEnum_spec
-- name    : EditMulticoloring.Dev.Ram.EncS.markEnum_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:31:45.602214+00:00
-- url     : https://prove2.me/theorems/add5a4d0-b646-4379-95f3-890d74885bb8
-- title:
--   EditMulticoloring.Dev.Ram.EncS.markEnum_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram.EncS`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem markEnum_spec {q : ℕ} (hq : 0 < q) (t r a ρ : ℕ) (chosen : List (Word q)) (st0 : HS)
--       (hρ : st0.regs r = ρ) (h7 : st0.regs (r + 7) = a + 1)
--       (x : Word q) (hx : x.length = ρ) (st : HS) (hI : MInv t r a ρ chosen st0 [] st)
--       (hlen : st.regs ((shortCfg r a).lenR (2 * t)) = x.length)
--       (hbuf : WordAt st ((shortCfg r a).buf (2 * t)) 0 x) :
--       MInv t r a ρ (chosen ++ [x]) st0 []
--         ((enumScripts q (2 * t) (shortCfg r a) (markBody q r a)).exec inp st) ∧
--       (enumScripts q (2 * t) (shortCfg r a) (markBody q r a)).cost inp B st ≤
--         (visits (2 * t) x).length * ((7 * ρ + 20) * kappa B (RAM.bits (shortM q t ρ a)) +
--           (shortCfg r a).enumE B q ρ (2 * t))
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.WordAt`, `EditMulticoloring.Dev.Ram.enumScripts`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.visits`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec`, `EditMulticoloring.Dev.Ram.EncS.MInv`, `EditMulticoloring.Dev.Ram.EncS.markBody`, `EditMulticoloring.Dev.Ram.EncS.shortCfg`, `EditMulticoloring.Dev.Ram.EncS.shortM`, `EditMulticoloring.Dev.Ram.EnumCfg.buf`, `EditMulticoloring.Dev.Ram.EnumCfg.enumE` and `EditMulticoloring.Dev.Ram.EnumCfg.lenR` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proof of `EditMulticoloring.Dev.Ram.EncS.mainBody_spec` of this split imports it.
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

namespace EditMulticoloring.Dev.Ram.EncS

open EditMulticoloring.Code

section Mark
variable (inp : ℕ → ℕ) (B : ℕ)

theorem markEnum_spec {q : ℕ} (hq : 0 < q) (t r a ρ : ℕ) (chosen : List (Word q)) (st0 : HS)
    (hρ : st0.regs r = ρ) (h7 : st0.regs (r + 7) = a + 1)
    (x : Word q) (hx : x.length = ρ) (st : HS) (hI : MInv t r a ρ chosen st0 [] st)
    (hlen : st.regs ((shortCfg r a).lenR (2 * t)) = x.length)
    (hbuf : WordAt st ((shortCfg r a).buf (2 * t)) 0 x) :
    MInv t r a ρ (chosen ++ [x]) st0 []
      ((enumScripts q (2 * t) (shortCfg r a) (markBody q r a)).exec inp st) ∧
    (enumScripts q (2 * t) (shortCfg r a) (markBody q r a)).cost inp B st ≤
      (visits (2 * t) x).length * ((7 * ρ + 20) * kappa B (RAM.bits (shortM q t ρ a)) +
        (shortCfg r a).enumE B q ρ (2 * t)) := by
  sorry

end Mark

end EditMulticoloring.Dev.Ram.EncS
end
