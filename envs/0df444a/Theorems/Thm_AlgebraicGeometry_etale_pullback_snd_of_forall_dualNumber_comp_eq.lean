-- Prove2me | Theorems.Thm_AlgebraicGeometry_etale_pullback_snd_of_forall_dualNumber_comp_eq
-- name    : AlgebraicGeometry.etale_pullback_snd_of_forall_dualNumber_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/65a8e36c-61c5-5dec-9ed0-296a950e9a51
-- title:
--   Étale fibre from injectivity on dual-number points
-- statement:
--   Let $k$ be an algebraically closed field, let $X$ and $Y$ be schemes, and let $f : X \to \operatorname{Spec} k$ and $g : Y \to \operatorname{Spec} k$ be morphisms that are locally of finite type. Let $\varphi : X \to Y$ satisfy $g \circ \varphi = f$, so that $\varphi$ is a morphism over $k$. Write $k[\varepsilon] =$ `DualNumber k` for the dual numbers over $k$ and $\varepsilon_0 : \operatorname{Spec} k[\varepsilon] \to \operatorname{Spec} k$ for the morphism induced by the structure map $k \to k[\varepsilon]$. Assume that $\varphi$ is injective on those $k[\varepsilon]$-points of $X$ which lie over $\varepsilon_0$: for all $P, Q : \operatorname{Spec} k[\varepsilon] \to X$ with $f \circ P = \varepsilon_0$ and $f \circ Q = \varepsilon_0$, the equality $\varphi \circ P = \varphi \circ Q$ forces $P = Q$. Finally let $y : \operatorname{Spec} k \to Y$ be a section of $g$, i.e. $g \circ y = \mathrm{id}_{\operatorname{Spec} k}$. The conclusion is that the second projection $\operatorname{pullback.snd}\,\varphi\,y$ from the fibre product $X \times_{Y, y} \operatorname{Spec} k$ to $\operatorname{Spec} k$ is étale.
--
--   This is the infinitesimal (tangent-space) criterion for the fibre of $\varphi$ over a $k$-rational point of $Y$ to be étale over $k$, the geometric form of unramifiedness detected on points with values in the dual numbers. It is the first half of the argument for [`AlgebraicGeometry.formallyUnramified_of_forall_dualNumber_comp_eq`](thm.html#AlgebraicGeometry.formallyUnramified_of_forall_dualNumber_comp_eq), which is its only consumer.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_etale_pullback_snd_of_forall_dualNumber_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.etale_pullback_snd_of_forall_dualNumber_comp_eq
    (k : Type u) [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (φ : X ⟶ Y) (hφ : φ ≫ g = f)
    (hinj : ∀ P Q : Spec (CommRingCat.of (DualNumber k)) ⟶ X,
      P ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) →
      Q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) →
      P ≫ φ = Q ≫ φ → P = Q)
    (y : Spec (CommRingCat.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _) :
    Etale (pullback.snd φ y) := by sorry
