-- Prove2me | Theorems.Thm_ExpanderTheorem_expander_mixing
-- name    : ExpanderTheorem.expander_mixing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:41:16.659926+00:00
-- url     : https://prove2.me/theorems/5256a8df-4eac-4e1c-a640-19e44674e2ab
-- title:
--   Expander Theorem: expander mixing
-- statement:
--   **The expander mixing lemma (Alon–Chung 1988).**
--
--   Source: https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/Solution.lean#L37-L43
-- source:
--   https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/Solution.lean#L37-L43

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

theorem ExpanderTheorem.expander_mixing (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : G.IsRegularOfDegree d) (hV : 2 ≤ Fintype.card V) {μ : ℝ}
    (hμ : ∀ x : V → ℝ, ∑ v, x v = 0 → |dotProduct x (G.adjMatrix ℝ *ᵥ x)| ≤ μ * dotProduct x x)
    (S T : Finset V) :
    |(edgeCount G S T : ℝ) - d * S.card * T.card / Fintype.card V| ≤
      μ * Real.sqrt (S.card * T.card) := by sorry
