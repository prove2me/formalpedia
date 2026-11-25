-- Prove2me | Theorems.Thm_Expanders_abs_dotProduct_adjMatrix_le
-- name    : Expanders.abs_dotProduct_adjMatrix_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:18:57.557691+00:00
-- url     : https://prove2.me/theorems/6c4d1d51-c7e4-4066-835f-bf9cbd612ac4
-- title:
--   Expanders: abs dot Product adj Matrix le
-- statement:
--   Polarization of the adjacency form on the vectors orthogonal to `𝟙`.
--
--   Source: https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/MixingAux.lean#L33-L72
-- source:
--   https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/MixingAux.lean#L33-L72

module
public import Mathlib
public import Definitions.Def_ExpanderLib_MixingAux
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix
open Expanders
variable {V : Type*} [Fintype V]

theorem Expanders.abs_dotProduct_adjMatrix_le (G : SimpleGraph V) [DecidableRel G.Adj] {μ : ℝ}
    (hμ : ∀ x : V → ℝ, ∑ v, x v = 0 → |dotProduct x (G.adjMatrix ℝ *ᵥ x)| ≤ μ * dotProduct x x)
    (x y : V → ℝ) (hx : ∑ v, x v = 0) (hy : ∑ v, y v = 0) :
    |dotProduct x (G.adjMatrix ℝ *ᵥ y)| ≤
      μ * (Real.sqrt (dotProduct x x) * Real.sqrt (dotProduct y y)) := by sorry
