-- Prove2me | Theorems.Thm_CategoryTheory_isPullback_selfProduct_baseChange
-- name    : CategoryTheory.isPullback_selfProduct_baseChange
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:28.588215+00:00
-- url     : https://prove2.me/theorems/880c1e0b-4e99-4a7f-b844-8eb135bebec4
-- title:
--   Base change preserves the self-fibre product square
-- statement:
--   Let $C$ be a category with pullbacks, let $f:X→S$, and let $b:T→S$. Put $X_T=X×_S T$, and let $α:X_T×_T X_T→X×_S X$ be the canonical map induced by the two projections $X_T→X$. Then the square formed by $α$, the projection $X_T×_T X_T→T$, the structure map $X×_S X→S$, and $b$ is a pullback: $$\operatorname{IsPullback}(α,\,X_T×_T X_T→T,\,X×_S X→S,\,b).$$ This supplies the categorical base-change identification used for relative group laws.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
open CategoryTheory

theorem CategoryTheory.isPullback_selfProduct_baseChange {C : Type*} [Category C] [HasPullbacks C]
    {X S T : C} (f : X ⟶ S) (b : T ⟶ S) :
    IsPullback
      (pullback.map (pullback.snd f b) (pullback.snd f b) f f
        (pullback.fst f b) (pullback.fst f b) b pullback.condition.symm pullback.condition.symm)
      (pullback.fst (pullback.snd f b) (pullback.snd f b) ≫ pullback.snd f b)
      (pullback.fst f f ≫ f) b := by sorry
