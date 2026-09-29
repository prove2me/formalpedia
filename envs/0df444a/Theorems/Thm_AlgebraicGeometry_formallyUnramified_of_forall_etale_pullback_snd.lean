-- Prove2me | Theorems.Thm_AlgebraicGeometry_formallyUnramified_of_forall_etale_pullback_snd
-- name    : AlgebraicGeometry.formallyUnramified_of_forall_etale_pullback_snd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/e1cd2903-c7ea-59e3-8054-bf464565815d
-- title:
--   Formal unramifiedness from étale fibres over k-points
-- statement:
--   Let $k$ be an algebraically closed field, and let $X$, $Y$ be schemes with structure morphisms $f : X \to \operatorname{Spec} k$ and $g : Y \to \operatorname{Spec} k$, each assumed locally of finite type. Let $\varphi : X \to Y$ be a morphism of schemes compatible with these structures, in the sense that $\varphi$ followed by $g$ equals $f$. Assume that for every morphism $y : \operatorname{Spec} k \to Y$ which is a section of $g$ (that is, $y$ followed by $g$ is the identity of $\operatorname{Spec} k$), hence for every $k$-rational point of $Y$, the second projection $X \times_Y \operatorname{Spec} k \to \operatorname{Spec} k$ of the pullback of $\varphi$ along $y$ is étale. The conclusion is that $\varphi$ is formally unramified, i.e. $\varphi$ has the unicity part of the infinitesimal lifting property: lifts along nilpotent thickenings, when they exist, are unique. Note that étaleness is required only of the fibres over $k$-rational points of $Y$, not of all fibres.
--
--   This is the fibrewise criterion for unramifiedness over an algebraically closed base (EGA IV₄ 17.4.1–17.4.2): for morphisms locally of finite type between schemes of finite type over $k = \bar k$, formal unramifiedness of $\varphi$ may be tested on the fibres over the $k$-points of $Y$, which are exactly the closed points. It feeds the criterion [`AlgebraicGeometry.formallyUnramified_of_forall_dualNumber_comp_eq`](thm.html#AlgebraicGeometry.formallyUnramified_of_forall_dualNumber_comp_eq), which reformulates the same conclusion in terms of morphisms from the spectrum of the dual numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_formallyUnramified_of_forall_etale_pullback_snd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.formallyUnramified_of_forall_etale_pullback_snd
    (k : Type u) [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (φ : X ⟶ Y) (hφ : φ ≫ g = f)
    (het : ∀ (y : Spec (CommRingCat.of k) ⟶ Y), y ≫ g = 𝟙 _ → Etale (pullback.snd φ y)) :
    FormallyUnramified φ := by sorry
