-- Prove2me | Theorems.Thm_ClassicalComplexWPT_exists_open_preparation_neighborhood
-- name    : ClassicalComplexWPT.exists_open_preparation_neighborhood
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:15:25.34945+00:00
-- url     : https://prove2.me/theorems/31c98c22-bbe9-4b43-be7e-49b42ce89c0c
-- title:
--   Classical Complex WPT: exists open preparation neighborhood
-- statement:
--   Explicit-neighborhood form of preparation: the same witnesses factor `f`
--   pointwise on an open neighborhood of the origin, throughout which the unit is
--   nonzero.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/Main.lean#L39-L58
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/Main.lean#L39-L58

import Definitions.Def_ClassicalComplexWPT_PreparationUniqueness
import Definitions.Def_ClassicalComplexWPT_PublicExistence
import Definitions.Def_ClassicalComplexWPT_Main
set_option autoImplicit true
open Filter
open scoped BigOperators Topology
open ClassicalComplexWPT

theorem ClassicalComplexWPT.exists_open_preparation_neighborhood
    (n d : ℕ) (f : Ambient n → ℂ)
    (hf : AnalyticAt ℂ f 0)
    (horder : ExactOrderInLastVariable f d) :
    ∃ (a : Fin d → Base n → ℂ) (u : Ambient n → ℂ) (s : Set (Ambient n)),
      IsWeierstrassPreparation f d a u ∧
      IsOpen s ∧ (0 : Ambient n) ∈ s ∧
      (∀ x ∈ s, u x ≠ 0) ∧
      ∀ x ∈ s, f x = u x * preparedPolynomial d a x := by sorry
