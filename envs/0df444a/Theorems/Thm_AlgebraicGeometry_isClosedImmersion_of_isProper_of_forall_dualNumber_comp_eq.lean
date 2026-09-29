-- Prove2me | Theorems.Thm_AlgebraicGeometry_isClosedImmersion_of_isProper_of_forall_dualNumber_comp_eq
-- name    : AlgebraicGeometry.isClosedImmersion_of_isProper_of_forall_dualNumber_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/617af6e3-82cd-5b65-852b-1fad29683ba2
-- title:
--   Closed immersion from injectivity on dual-number points
-- statement:
--   Let $k$ be an algebraically closed field and let $X,Y$ be schemes (in a fixed universe). Let $f\colon X\to\operatorname{Spec} k$ be a proper morphism, let $g\colon Y\to\operatorname{Spec} k$ be separated and locally of finite type, and let $\varphi\colon X\to Y$ be a morphism over $k$, in the sense that $\varphi$ followed by $g$ equals $f$. Write $k[\varepsilon]$ for the dual numbers over $k$ and $\iota_\varepsilon=\operatorname{Spec}$ of the structure map $k\to k[\varepsilon]$. Assume that $\varphi$ is injective on $k[\varepsilon]$-valued points of $X$ over $k$: for all morphisms $P,Q\colon\operatorname{Spec} k[\varepsilon]\to X$ with $P$ followed by $f$ and $Q$ followed by $f$ both equal to $\iota_\varepsilon$, if $P$ followed by $\varphi$ equals $Q$ followed by $\varphi$, then $P=Q$. The conclusion is that $\varphi$ is a closed immersion. Note that the finiteness hypothesis on the source is not imposed separately: it is supplied by properness of $f$.
--
--   This is the standard criterion that a proper morphism of $k$-schemes which separates $k$-points and tangent vectors at $k$-points (here packaged as injectivity on $k[\varepsilon]$-valued points) is a closed immersion. It is used in the project to recognise closed immersions built from sections of a line bundle, and in the Čerednik–Drinfel'd material on fake elliptic curves and period maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isClosedImmersion_of_isProper_of_forall_dualNumber_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isClosedImmersion_of_isProper_of_forall_dualNumber_comp_eq
    (k : Type u) [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (g : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated g] [LocallyOfFiniteType g]
    (φ : X ⟶ Y) (hφ : φ ≫ g = f)
    (hinj : ∀ P Q : Spec (CommRingCat.of (DualNumber k)) ⟶ X,
      P ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) →
      Q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) →
      P ≫ φ = Q ≫ φ → P = Q) :
    IsClosedImmersion φ := by sorry
