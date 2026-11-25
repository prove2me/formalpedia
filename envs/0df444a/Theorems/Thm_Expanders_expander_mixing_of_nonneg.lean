-- Prove2me | Theorems.Thm_Expanders_expander_mixing_of_nonneg
-- name    : Expanders.expander_mixing_of_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:29:27.76053+00:00
-- url     : https://prove2.me/theorems/c1ecee36-5ed6-5928-936f-2d44e24f9bb4
-- title:
--   Expanders: expander mixing of nonneg
-- statement:
--   **The expander mixing lemma (Alon–Chung 1988)**, with `0 ≤ μ`.
--
--   Source: https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/Expanders.lean#L46-L129
-- source:
--   https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/Expanders.lean#L46-L129

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

theorem Expanders.expander_mixing_of_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : G.IsRegularOfDegree d) {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : V → ℝ, ∑ v, x v = 0 → |dotProduct x (G.adjMatrix ℝ *ᵥ x)| ≤ μ * dotProduct x x)
    (S T : Finset V) :
    |(edgeCount G S T : ℝ) - d * S.card * T.card / Fintype.card V| ≤
      μ * Real.sqrt (S.card * T.card) := by sorry
