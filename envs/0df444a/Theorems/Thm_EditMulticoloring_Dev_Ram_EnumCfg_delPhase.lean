-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_EnumCfg_delPhase
-- name    : EditMulticoloring.Dev.Ram.EnumCfg.delPhase
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:31:57.502185+00:00
-- url     : https://prove2.me/theorems/670d464c-effe-46a6-ada6-8e8d3c801e7b
-- title:
--   EditMulticoloring.Dev.Ram.EnumCfg.delPhase (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram.EnumCfg`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem delPhase (hstable : ∀ a st st', Inv a st → c.Agree s st st' → Inv a st')
--       (k : ℕ) (hk : k + 1 ≤ s) (IH : c.IHk inp B s L body Inv f cb Ok k)
--       (x : Word q) (hxL : x.length + (k + 1) ≤ L + s) (a0 : α)
--       (hok : ∀ j (hj : j < (visits (k + 1) x).length),
--         Ok (((visits (k + 1) x).take j).foldl f a0) ((visits (k + 1) x)[j]))
--       (st0 : HS) (hlen0 : st0.regs (c.lenR (k + 1)) = x.length)
--       (hx0 : WordAt st0 (c.buf (k + 1)) 0 x) (acc : α) (st : HS)
--       (Pre Post : List (Word q))
--       (hV : visits (k + 1) x = Pre ++ ((List.range x.length).flatMap (fun i => visits k (delW x i))) ++ Post)
--       (hacc : acc = Pre.foldl f a0)
--       (hQ : c.LQ Inv s (k + 1) st0 acc st) (hcnt : st.regs c.cnt = x.length) :
--       c.LQ Inv s (k + 1) st0
--         (((List.range x.length).flatMap (fun i => visits k (delW x i))).foldl f acc)
--         ((c.delLoop q body k).exec inp st) ∧
--       (c.delLoop q body k).cost inp B st ≤
--         ((List.range x.length).flatMap (fun i => visits k (delW x i))).length *
--           (cb + c.enumE B q L s) +
--         20 * (q + 1) * (x.length + 2) ^ 2 * kappa B (RAM.bits (c.enumM q L s))
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.Cmd`, `EditMulticoloring.Dev.Ram.EnumCfg`, `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.WordAt`, `EditMulticoloring.Dev.Ram.delW`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.visits`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec`, `EditMulticoloring.Dev.Ram.EnumCfg.Agree`, `EditMulticoloring.Dev.Ram.EnumCfg.IHk`, `EditMulticoloring.Dev.Ram.EnumCfg.LQ`, `EditMulticoloring.Dev.Ram.EnumCfg.buf`, `EditMulticoloring.Dev.Ram.EnumCfg.cnt`, `EditMulticoloring.Dev.Ram.EnumCfg.delLoop`, `EditMulticoloring.Dev.Ram.EnumCfg.enumE`, `EditMulticoloring.Dev.Ram.EnumCfg.enumM` and `EditMulticoloring.Dev.Ram.EnumCfg.lenR` (definitions bundle `EMRamB000` of this split).
--
--   **Used by.** The proof of `EditMulticoloring.Dev.Ram.enumScripts_spec` of this split imports it.
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

namespace EnumCfg
variable (c : EnumCfg) (inp : ℕ → ℕ) (B : ℕ)

section Phases
variable {q : ℕ} {α : Type*} (s L : ℕ) (body : Cmd) (Inv : α → HS → Prop) (f : α → Word q → α)
  (cb : ℕ) (Ok : α → Word q → Prop)

theorem delPhase (hstable : ∀ a st st', Inv a st → c.Agree s st st' → Inv a st')
    (k : ℕ) (hk : k + 1 ≤ s) (IH : c.IHk inp B s L body Inv f cb Ok k)
    (x : Word q) (hxL : x.length + (k + 1) ≤ L + s) (a0 : α)
    (hok : ∀ j (hj : j < (visits (k + 1) x).length),
      Ok (((visits (k + 1) x).take j).foldl f a0) ((visits (k + 1) x)[j]))
    (st0 : HS) (hlen0 : st0.regs (c.lenR (k + 1)) = x.length)
    (hx0 : WordAt st0 (c.buf (k + 1)) 0 x) (acc : α) (st : HS)
    (Pre Post : List (Word q))
    (hV : visits (k + 1) x = Pre ++ ((List.range x.length).flatMap (fun i => visits k (delW x i))) ++ Post)
    (hacc : acc = Pre.foldl f a0)
    (hQ : c.LQ Inv s (k + 1) st0 acc st) (hcnt : st.regs c.cnt = x.length) :
    c.LQ Inv s (k + 1) st0
      (((List.range x.length).flatMap (fun i => visits k (delW x i))).foldl f acc)
      ((c.delLoop q body k).exec inp st) ∧
    (c.delLoop q body k).cost inp B st ≤
      ((List.range x.length).flatMap (fun i => visits k (delW x i))).length *
        (cb + c.enumE B q L s) +
      20 * (q + 1) * (x.length + 2) ^ 2 * kappa B (RAM.bits (c.enumM q L s)) := by
  sorry

end Phases

end EnumCfg

end EditMulticoloring.Dev.Ram
end
