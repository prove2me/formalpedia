-- Prove2me | Theorems.Thm_EditMulticoloring_Dev_Ram_EnumCfg_repPhase
-- name    : EditMulticoloring.Dev.Ram.EnumCfg.repPhase
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-19T15:31:43.493676+00:00
-- url     : https://prove2.me/theorems/c478ba00-c4e5-4e90-9f55-77fec2d4a1cc
-- title:
--   EditMulticoloring.Dev.Ram.EnumCfg.repPhase (intermediate lemma)
-- statement:
--   An intermediate lemma of the split of the formal proof of `EditMulticoloring.Code.ram_programs`, carved for this platform from the Lean development *RAM programs for the explicit edit codes of the multicoloring construction (STOC 2027 submission 819): encoder and decoder written in a structured language compiled to the mission's RAM model, with exact outputs and bit-cost bounds* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes the leaf `EditMulticoloring.Code.ram_programs` of the goal of the prove2.me mission Explicit Edit Codes via Multicoloring (STOC 2027 submission 819). It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `EditMulticoloring.Dev.Ram.EnumCfg`, with `open EditMulticoloring.Code`):
--
--   ```lean
--   theorem repPhase (hstable : ∀ a st st', Inv a st → c.Agree s st st' → Inv a st')
--       (k : ℕ) (hk : k + 1 ≤ s) (IH : c.IHk inp B s L body Inv f cb Ok k)
--       (x : Word q) (hxL : x.length + (k + 1) ≤ L + s) (a0 : α)
--       (hok : ∀ j (hj : j < (visits (k + 1) x).length),
--         Ok (((visits (k + 1) x).take j).foldl f a0) ((visits (k + 1) x)[j]))
--       (st0 : HS) (hlen0 : st0.regs (c.lenR (k + 1)) = x.length)
--       (hx0 : WordAt st0 (c.buf (k + 1)) 0 x) (acc : α) (st : HS)
--       (Pre Post : List (Word q))
--       (hV : visits (k + 1) x = Pre ++ ((List.range x.length).flatMap (fun i =>
--             (List.range q).flatMap (finFlat fun b =>
--               if x[i]? = some b then [] else visits k (repW x i b)))) ++ Post)
--       (hacc : acc = Pre.foldl f a0)
--       (hQ : c.LQ Inv s (k + 1) st0 acc st) (hcnt : st.regs c.cnt = x.length) :
--       c.LQ Inv s (k + 1) st0
--         (((List.range x.length).flatMap (fun i =>
--             (List.range q).flatMap (finFlat fun b =>
--               if x[i]? = some b then [] else visits k (repW x i b)))).foldl f acc)
--         ((c.repLoop q body k).exec inp st) ∧
--       (c.repLoop q body k).cost inp B st ≤
--         ((List.range x.length).flatMap (fun i =>
--             (List.range q).flatMap (finFlat fun b =>
--               if x[i]? = some b then [] else visits k (repW x i b)))).length *
--           (cb + c.enumE B q L s) +
--         20 * (q + 1) * (x.length + 2) ^ 2 * kappa B (RAM.bits (c.enumM q L s))
--   ```
--
--   **Definitions.** The statement is written with `EditMulticoloring.Dev.Ram.Cmd`, `EditMulticoloring.Dev.Ram.EnumCfg`, `EditMulticoloring.Dev.Ram.HS`, `EditMulticoloring.Dev.Ram.WordAt`, `EditMulticoloring.Dev.Ram.finFlat`, `EditMulticoloring.Dev.Ram.kappa`, `EditMulticoloring.Dev.Ram.repW`, `EditMulticoloring.Dev.Ram.visits`, `EditMulticoloring.Dev.Ram.Cmd.cost`, `EditMulticoloring.Dev.Ram.Cmd.exec`, `EditMulticoloring.Dev.Ram.EnumCfg.Agree`, `EditMulticoloring.Dev.Ram.EnumCfg.IHk`, `EditMulticoloring.Dev.Ram.EnumCfg.LQ`, `EditMulticoloring.Dev.Ram.EnumCfg.buf`, `EditMulticoloring.Dev.Ram.EnumCfg.cnt`, `EditMulticoloring.Dev.Ram.EnumCfg.enumE`, `EditMulticoloring.Dev.Ram.EnumCfg.enumM`, `EditMulticoloring.Dev.Ram.EnumCfg.lenR` and `EditMulticoloring.Dev.Ram.EnumCfg.repLoop` (definitions bundle `EMRamB000` of this split).
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

set_option maxHeartbeats 1000000 in
theorem repPhase (hstable : ∀ a st st', Inv a st → c.Agree s st st' → Inv a st')
    (k : ℕ) (hk : k + 1 ≤ s) (IH : c.IHk inp B s L body Inv f cb Ok k)
    (x : Word q) (hxL : x.length + (k + 1) ≤ L + s) (a0 : α)
    (hok : ∀ j (hj : j < (visits (k + 1) x).length),
      Ok (((visits (k + 1) x).take j).foldl f a0) ((visits (k + 1) x)[j]))
    (st0 : HS) (hlen0 : st0.regs (c.lenR (k + 1)) = x.length)
    (hx0 : WordAt st0 (c.buf (k + 1)) 0 x) (acc : α) (st : HS)
    (Pre Post : List (Word q))
    (hV : visits (k + 1) x = Pre ++ ((List.range x.length).flatMap (fun i =>
          (List.range q).flatMap (finFlat fun b =>
            if x[i]? = some b then [] else visits k (repW x i b)))) ++ Post)
    (hacc : acc = Pre.foldl f a0)
    (hQ : c.LQ Inv s (k + 1) st0 acc st) (hcnt : st.regs c.cnt = x.length) :
    c.LQ Inv s (k + 1) st0
      (((List.range x.length).flatMap (fun i =>
          (List.range q).flatMap (finFlat fun b =>
            if x[i]? = some b then [] else visits k (repW x i b)))).foldl f acc)
      ((c.repLoop q body k).exec inp st) ∧
    (c.repLoop q body k).cost inp B st ≤
      ((List.range x.length).flatMap (fun i =>
          (List.range q).flatMap (finFlat fun b =>
            if x[i]? = some b then [] else visits k (repW x i b)))).length *
        (cb + c.enumE B q L s) +
      20 * (q + 1) * (x.length + 2) ^ 2 * kappa B (RAM.bits (c.enumM q L s)) := by
  sorry

end Phases

end EnumCfg

end EditMulticoloring.Dev.Ram
end
