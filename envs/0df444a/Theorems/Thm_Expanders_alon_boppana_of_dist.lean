-- Prove2me | Theorems.Thm_Expanders_alon_boppana_of_dist
-- name    : Expanders.alon_boppana_of_dist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:30:05.941694+00:00
-- url     : https://prove2.me/theorems/1b062686-8b47-43f3-a857-cc2f6e05abdd
-- title:
--   Expanders: alon boppana of dist
-- statement:
--   **The Alon–Boppana bound (Nilli 1991)**, corrected: the original statement with the
--   hypothesis `2 * k + 2 ≤ G.dist u w` strengthened to `2 * k + 4 ≤ G.dist u w`. The original
--   hypothesis `G.Reachable u w` is dropped, since it follows from `G.dist u w ≠ 0`.
--
--   Source: https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/Expanders.lean#L155-L220
-- source:
--   https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/Expanders.lean#L155-L220

module
public import Mathlib
public import Definitions.Def_ExpanderLib_MixingAux
public import Definitions.Def_ExpanderLib_NilliBall
public import Definitions.Def_ExpanderLib_Expanders
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix
open Expanders
variable {V : Type*} [Fintype V]

theorem Expanders.alon_boppana_of_dist (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (hd2 : 2 ≤ d)
    (hd : G.IsRegularOfDegree d) {k : ℕ} {u w : V} (huw : 2 * k + 4 ≤ G.dist u w) :
    ∃ x : V → ℝ, x ≠ 0 ∧ ∑ v, x v = 0 ∧
      (2 * Real.sqrt (d - 1) - (2 * Real.sqrt (d - 1) - 1) / (k + 1)) * dotProduct x x ≤
        dotProduct x (G.adjMatrix ℝ *ᵥ x) := by sorry
