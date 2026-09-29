-- Prove2me | Theorems.Thm_AlgebraicGeometry_flat_iff_forall_appLE_mul_eq_zero_of_isDedekindDomain
-- name    : AlgebraicGeometry.flat_iff_forall_appLE_mul_eq_zero_of_isDedekindDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/ca8b09c8-e508-5512-8960-c709cdf5e545
-- title:
--   Flatness over a Dedekind domain via torsion-free sections
-- statement:
--   Let $R$ be a commutative ring that is a Dedekind domain, let $X$ be a scheme and let $f : X \to \operatorname{Spec} R$ be a morphism of schemes, where $\operatorname{Spec} R$ is the spectrum of $R$ viewed as an object of `CommRingCat`. The assertion is an equivalence. On one side stands the Mathlib morphism property `Flat f`, flatness of $f$. On the other stands the following condition: for every affine open $U$ of $X$ (that is, every element of `X.affineOpens`: an open subset together with the property of being affine), every $c \in R$ and every section $s \in \Gamma(X, U)$, if $c \neq 0$ and the product of $s$ with the image of $c$ under the ring homomorphism $\Gamma(X, U)$ obtained as the inverse of the canonical isomorphism $R \cong \Gamma(\operatorname{Spec} R, \top)$ followed by $f^{\ast} =$ `f.appLE ⊤ U le_top` vanishes, then $s = 0$. In other words, $f$ is flat precisely when each ring of sections $\Gamma(X, U)$ over an affine open $U \subseteq X$ is torsion-free as an $R$-module for the $R$-algebra structure induced by $f$.
--
--   This is the standard criterion that over a Dedekind base flatness of a morphism is equivalent to absence of $R$-torsion in the rings of sections over affine opens, in the form of a workable test on affine charts. It is used to verify flatness of integral models, in particular in the proof of a flatness statement for germs at closed points and in the flatness of the fine moduli scheme occurring in the Čerednik–Drinfel'd setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_flat_iff_forall_appLE_mul_eq_zero_of_isDedekindDomain.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.flat_iff_forall_appLE_mul_eq_zero_of_isDedekindDomain
    {R : Type u} [CommRing R] [IsDedekindDomain R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    Flat f ↔ ∀ (U : X.affineOpens) (c : R) (s : Γ(X, U)), c ≠ 0 →
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top) c * s = 0 → s = 0 := by sorry
