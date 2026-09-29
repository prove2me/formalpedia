-- Prove2me | Theorems.Thm_CategoryTheory_IsPullback_fst_pullbackMap_of_comp_eq
-- name    : CategoryTheory.IsPullback.fst_pullbackMap_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/5b13e0a2-f8ec-5f6f-ab83-b8db1890499c
-- title:
--   Base change along t is a pullback of π
-- statement:
--   Let $\mathcal C$ be a category, and let $X$, $X'$, $S$, $T$ be objects of $\mathcal C$. Given morphisms $f\colon X\to S$, $f'\colon X'\to S$, $t\colon T\to S$ and $\pi\colon X'\to X$ with $\pi$ a morphism over $S$, i.e. $\pi$ followed by $f$ equals $f'$, and assuming that the pullbacks of $f$ along $t$ and of $f'$ along $t$ exist, consider the induced morphism $\pi\times_S T \colon X'\times_S T\to X\times_S T$ given by `pullback.map f' t f t π (𝟙 T) (𝟙 S)` — the unique morphism whose composite with the first projection is the first projection followed by $\pi$ and whose composite with the second projection is the second projection. The assertion is that the square with upper-left vertex $X'\times_S T$, top edge the first projection $X'\times_S T\to X'$, left edge $\pi\times_S T$, right edge $\pi\colon X'\to X$ and bottom edge the first projection $X\times_S T\to X$ is a pullback square: it commutes, and the resulting cone exhibits $X'\times_S T$ as the fibre product of $X'$ and $X\times_S T$ over $X$.
--
--   This is the standard consequence of the pasting law for cartesian squares saying that forming the fibre product with $T$ over $S$ realises the base change $\pi\times_S T$ as a pullback of $\pi$ itself. It is the square used in the relative Picard constructions of the project, where properties of morphisms stable under base change, and invariants such as the rank of a finite locally free morphism, are transported from $\pi$ to $\pi\times_S T$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CategoryTheory_IsPullback_fst_pullbackMap_of_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe v w u

open CategoryTheory CategoryTheory.Limits

theorem CategoryTheory.IsPullback.fst_pullbackMap_of_comp_eq {C : Type w} [Category.{v} C] {X X' S T : C}
    (f : X ⟶ S) (f' : X' ⟶ S) (t : T ⟶ S) (π : X' ⟶ X) (hπ : π ≫ f = f')
    [HasPullback f t] [HasPullback f' t] :
    IsPullback (pullback.fst f' t)
      (pullback.map f' t f t π (𝟙 T) (𝟙 S) (by rw [Category.comp_id, hπ]) (by rw [Category.comp_id, Category.id_comp]))
      π (pullback.fst f t) := by sorry
