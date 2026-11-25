-- Prove2me | Theorems.Thm_Expanders_expander_mixing_of_two_le_card
-- name    : Expanders.expander_mixing_of_two_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:29:58.248227+00:00
-- url     : https://prove2.me/theorems/8340531d-f2ec-49c0-bdfa-70141e262ee0
-- title:
--   Expanders: expander mixing of two le card
-- statement:
--   **The expander mixing lemma (Alon–Chung 1988)** for graphs with at least two vertices: here
--   the original hypotheses already force `0 ≤ μ`.
--
--   Source: https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/Expanders.lean#L133-L150
-- source:
--   https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/Expanders.lean#L133-L150

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

theorem Expanders.expander_mixing_of_two_le_card (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : G.IsRegularOfDegree d) (hV : 2 ≤ Fintype.card V) {μ : ℝ}
    (hμ : ∀ x : V → ℝ, ∑ v, x v = 0 → |dotProduct x (G.adjMatrix ℝ *ᵥ x)| ≤ μ * dotProduct x x)
    (S T : Finset V) :
    |(edgeCount G S T : ℝ) - d * S.card * T.card / Fintype.card V| ≤
      μ * Real.sqrt (S.card * T.card) := by sorry
