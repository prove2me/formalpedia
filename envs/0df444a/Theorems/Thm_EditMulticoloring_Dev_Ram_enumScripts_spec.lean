-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_enumScripts_spec
-- name    : EditMulticoloring.Dev.Ram.enumScripts_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:33:44.504453+00:00
-- url     : https://prove2.me/theorems/0d3ed011-8dbd-4d08-8e8b-cb9f6092f9b1
-- title:
--   EditMulticoloring.Dev.Ram.enumScripts_spec (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem enumScripts_spec {q : ℕ} {α : Type*} (s : ℕ) (cfg : EnumCfg) (body : Cmd)
--       (inp : ℕ → ℕ) (B : ℕ) (Inv : α → HS → Prop) (f : α → Word q → α) (cb : ℕ)
--       (x : Word q) (a0 : α)
--       (hstable : ∀ a st st', Inv a st → cfg.Agree s st st' → Inv a st')
--       (hbody : ∀ a st (w : Word q) (j : ℕ) (hj : j < (visits s x).length),
--         w = (visits s x)[j] → a = ((visits s x).take j).foldl f a0 →
--         Inv a st → st.regs cfg.VL = w.length → WordAt st cfg.vis 0 w →
--         Inv (f a w) (body.exec inp st) ∧ cfg.BodyFrame s st (body.exec inp st) ∧
--         body.cost inp B st ≤ cb)
--       (st : HS) (hlen : st.regs (cfg.lenR s) = x.length) (hx : WordAt st (cfg.buf s) 0 x)
--       (ha : Inv a0 st) :
--       Inv ((visits s x).foldl f a0) ((enumScripts q s cfg body).exec inp st) ∧
--       ((enumScripts q s cfg body).exec inp st).regs (cfg.lenR s) = x.length ∧
--       WordAt ((enumScripts q s cfg body).exec inp st) (cfg.buf s) 0 x ∧
--       (enumScripts q s cfg body).cost inp B st ≤
--         (visits s x).length * (cb + cfg.enumE B q x.length s)
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.Cmd`, `EditMulticoloring.Dev.Ram.EnumCfg`, `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.WordAt`, `EditMulticoloring.Dev.Ram.enumScripts`, `EditMulticoloring.Dev.Ram.visits`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec`, `EditMulticoloring.Dev.Ram.EnumCfg.Agree`, `EditMulticoloring.Dev.Ram.EnumCfg.BodyFrame`, `EditMulticoloring.Dev.Ram.EnumCfg.VL`, `EditMulticoloring.Dev.Ram.EnumCfg.buf`, `EditMulticoloring.Dev.Ram.EnumCfg.enumE`, `EditMulticoloring.Dev.Ram.EnumCfg.lenR` and `EditMulticoloring.Dev.Ram.EnumCfg.vis` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proofs of `EditMulticoloring.Dev.Ram.EncS.markEnum_spec`, `EditMulticoloring_Dev_Ram_colorEnum_spec`, `EditMulticoloring.Dev.Ram.colorOf_spec`, `EditMulticoloring.Dev.Ram.colorsAll_spec` and `EditMulticoloring.Dev.Ram.decEnum_spec` of this split import it.
-- source:
--   the submitter, written with Claude, RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds; after the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819)

import Mathlib
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

theorem enumScripts_spec {q : ℕ} {α : Type*} (s : ℕ) (cfg : EnumCfg) (body : Cmd)
    (inp : ℕ → ℕ) (B : ℕ) (Inv : α → HS → Prop) (f : α → Word q → α) (cb : ℕ)
    (x : Word q) (a0 : α)
    (hstable : ∀ a st st', Inv a st → cfg.Agree s st st' → Inv a st')
    (hbody : ∀ a st (w : Word q) (j : ℕ) (hj : j < (visits s x).length),
      w = (visits s x)[j] → a = ((visits s x).take j).foldl f a0 →
      Inv a st → st.regs cfg.VL = w.length → WordAt st cfg.vis 0 w →
      Inv (f a w) (body.exec inp st) ∧ cfg.BodyFrame s st (body.exec inp st) ∧
      body.cost inp B st ≤ cb)
    (st : HS) (hlen : st.regs (cfg.lenR s) = x.length) (hx : WordAt st (cfg.buf s) 0 x)
    (ha : Inv a0 st) :
    Inv ((visits s x).foldl f a0) ((enumScripts q s cfg body).exec inp st) ∧
    ((enumScripts q s cfg body).exec inp st).regs (cfg.lenR s) = x.length ∧
    WordAt ((enumScripts q s cfg body).exec inp st) (cfg.buf s) 0 x ∧
    (enumScripts q s cfg body).cost inp B st ≤
      (visits s x).length * (cb + cfg.enumE B q x.length s) := by
  sorry

end EditMulticoloring.Dev.Ram
end
