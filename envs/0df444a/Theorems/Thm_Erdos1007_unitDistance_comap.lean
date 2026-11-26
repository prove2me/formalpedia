-- Prove2me | Theorems.Thm_Erdos1007_unitDistance_comap
-- name    : Erdos1007.unitDistance_comap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:53:19.912977+00:00
-- url     : https://prove2.me/theorems/484a5cfa-fc8d-5f1c-97bc-416bbeb72fc7
-- title:
--   Erdos1007: unit Distance comap
-- statement:
--   A unit-distance representation of `G` in `ℝⁿ` pulls back along an injective homomorphism
--   `φ : H →g G` (blueprint node `lem:monotone`).
--
--   The placement of `H` is the placement of `G` precomposed with `φ`. Injectivity of both maps keeps
--   the placement injective, and `φ` sends edges of `H` to edges of `G`. Chaffee–Noble Lemma 4,
--   attributed there to Erdős–Harary–Tutte.
--
--   Source: https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/UnitDistanceComap.lean#L42-L51
-- source:
--   https://github.com/Dishah3241/Erdos1007/blob/43f89415a6663848a1445effbda8b3abe77b052b/Erdos1007/Geometry/UnitDistanceComap.lean#L42-L51

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Definitions.Def_Erdos1007_Geometry_UnitDistanceComap
set_option autoImplicit false
@[expose] public section
open Erdos1007
open SimpleGraph
public section

theorem Erdos1007.unitDistance_comap {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {n : ℕ}
    (φ : H →g G) (hφ : Function.Injective φ) :
    (∃ f : V → EuclideanSpace ℝ (Fin n), Function.Injective f ∧
        ∀ u v, G.Adj u v → dist (f u) (f v) = 1) →
      ∃ g : W → EuclideanSpace ℝ (Fin n), Function.Injective g ∧
        ∀ u v, H.Adj u v → dist (g u) (g v) = 1 := by sorry
