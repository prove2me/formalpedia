-- Prove2me | Theorems.Thm_ExpanderTheorem_alon_boppana
-- name    : ExpanderTheorem.alon_boppana
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:41:22.991049+00:00
-- url     : https://prove2.me/theorems/88a4a012-5509-41b3-98be-00474ada23b0
-- title:
--   Expander Theorem: alon boppana
-- statement:
--   **The Alon–Boppana bound (Nilli 1991)**, for two vertices at distance at least `2k + 4`.
--
--   Source: https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/Solution.lean#L46-L51
-- source:
--   https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/Solution.lean#L46-L51

module
public import Mathlib
public import Definitions.Def_ExpanderLib_Expanders
public import Definitions.Def_ExpanderSpectral_Solution
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix
open ExpanderTheorem
variable {V : Type*} [Fintype V]

theorem ExpanderTheorem.alon_boppana (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (hd2 : 2 ≤ d)
    (hd : G.IsRegularOfDegree d) {k : ℕ} {u w : V} (huw : 2 * k + 4 ≤ G.dist u w) :
    ∃ x : V → ℝ, x ≠ 0 ∧ ∑ v, x v = 0 ∧
      (2 * Real.sqrt (d - 1) - (2 * Real.sqrt (d - 1) - 1) / (k + 1)) * dotProduct x x ≤
        dotProduct x (G.adjMatrix ℝ *ᵥ x) := by sorry
