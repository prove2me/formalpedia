-- Prove2me | Theorems.Thm_Expanders_dotProduct_adjMatrix_mulVec_eq_zero
-- name    : Expanders.dotProduct_adjMatrix_mulVec_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:19:12.847142+00:00
-- url     : https://prove2.me/theorems/7d51b2fc-ce15-460f-b668-b6cb18e15b07
-- title:
--   Expanders: dot Product adj Matrix mul Vec eq zero
-- statement:
--   Cross terms of the quadratic form vanish for vectors supported on non-adjacent sets.
--
--   Source: https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L342-L353
-- source:
--   https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L342-L353

module
public import Mathlib
public import Definitions.Def_ExpanderLib_NilliBall
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open Expanders
variable {V : Type*} [Fintype V]

theorem Expanders.dotProduct_adjMatrix_mulVec_eq_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V → ℝ) (B₁ B₂ : Finset V) (hx : ∀ v, v ∉ B₁ → x v = 0) (hy : ∀ v, v ∉ B₂ → y v = 0)
    (hno : ∀ a ∈ B₁, ∀ b ∈ B₂, ¬ G.Adj a b) :
    dotProduct x (G.adjMatrix ℝ *ᵥ y) = 0 := by sorry
