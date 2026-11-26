-- Prove2me | Theorems.Thm_Erdos1007_unitDistance_of_fin_le
-- name    : Erdos1007.unitDistance_of_fin_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:53:15.651868+00:00
-- url     : https://prove2.me/theorems/c6cbfefa-cee9-4eaa-8f13-8a8449c9f253
-- title:
--   Erdos1007: unit Distance of fin le
-- statement:
--   A unit-distance representation of `G` in `ℝⁿ` yields one in `ℝᵐ` whenever `n ≤ m`.
--
--   The placement in `ℝᵐ` appends zero coordinates to the placement in `ℝⁿ`. Injectivity and edge
--   lengths are preserved because the extra coordinates agree.
--
--   Source: https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/FinLe.lean#L82-L90
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/FinLe.lean#L82-L90

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Function.Basic
public import Definitions.Def_Erdos1007_Geometry_FinLe
set_option autoImplicit false
@[expose] public section
open Erdos1007
noncomputable section
public section

theorem Erdos1007.unitDistance_of_fin_le {V : Type*} {G : SimpleGraph V} {n m : ℕ} (h : n ≤ m) :
    (∃ f : V → EuclideanSpace ℝ (Fin n), Function.Injective f ∧
        ∀ u v, G.Adj u v → dist (f u) (f v) = 1) →
      ∃ g : V → EuclideanSpace ℝ (Fin m), Function.Injective g ∧
        ∀ u v, G.Adj u v → dist (g u) (g v) = 1 := by sorry
