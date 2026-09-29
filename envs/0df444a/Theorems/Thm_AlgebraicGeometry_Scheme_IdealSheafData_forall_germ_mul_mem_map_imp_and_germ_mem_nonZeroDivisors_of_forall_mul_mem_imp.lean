-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_forall_germ_mul_mem_map_imp_and_germ_mem_nonZeroDivisors_of_forall_mul_mem_imp
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.forall_germ_mul_mem_map_imp_and_germ_mem_nonZeroDivisors_of_forall_mul_mem_imp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/40a15485-906d-5fa5-a198-f977c87ae4f9
-- title:
--   Saturation and regularity pass to the stalk
-- statement:
--   Let $X$ be a scheme, $I$ an ideal sheaf datum on $X$ (a `Scheme.IdealSheafData`, which assigns to each affine open $V$ an ideal $I.\mathrm{ideal}\,V \subseteq \Gamma(X,V)$ compatibly with localisation), let $U$ be an affine open of $X$, let $x$ be a point of $X$ lying in $U$, and let $t \in \Gamma(X,U)$. Assume that $I.\mathrm{ideal}\,U$ is $t$-saturated, i.e. for every $s \in \Gamma(X,U)$, $t s \in I.\mathrm{ideal}\,U$ implies $s \in I.\mathrm{ideal}\,U$, and that $t$ is a non-zero-divisor in $\Gamma(X,U)$. Write $t_x$ for the germ of $t$ at $x$ under the germ map $\Gamma(X,U) \to \mathcal{O}_{X,x}$ and let $J$ be the image ideal $(I.\mathrm{ideal}\,U)\cdot\mathcal{O}_{X,x}$, the pushforward of $I.\mathrm{ideal}\,U$ along that germ map. The conclusion is the conjunction of two assertions: first, $J$ is $t_x$-saturated, i.e. for every $r \in \mathcal{O}_{X,x}$ with $t_x r \in J$ one has $r \in J$; second, $t_x$ is a non-zero-divisor in the stalk $\mathcal{O}_{X,x}$.
--
--   This is the passage from an affine open to a stalk of the two standing hypotheses used in local principality arguments: saturation of an ideal with respect to a regular element, and regularity of that element. It is used in the construction of ideal-theoretic data on the model of the modular curve $X_1(p)$, where $t$ is a pulled-back uniformiser and $I$ the saturated closure of a divisor on the generic fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_forall_germ_mul_mem_map_imp_and_germ_mem_nonZeroDivisors_of_forall_mul_mem_imp.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

theorem AlgebraicGeometry.Scheme.IdealSheafData.forall_germ_mul_mem_map_imp_and_germ_mem_nonZeroDivisors_of_forall_mul_mem_imp
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) (x : ↥X) (hx : x ∈ (U : X.Opens)) (t : Γ(X, U))
    (hsat : ∀ s : Γ(X, U), t * s ∈ I.ideal U → s ∈ I.ideal U) (ht : t ∈ nonZeroDivisors Γ(X, U)) :
    (∀ r : X.presheaf.stalk x,
        X.presheaf.germ (U : X.Opens) x hx t * r ∈ (I.ideal U).map (X.presheaf.germ (U : X.Opens) x hx).hom →
          r ∈ (I.ideal U).map (X.presheaf.germ (U : X.Opens) x hx).hom) ∧
      X.presheaf.germ (U : X.Opens) x hx t ∈ nonZeroDivisors (X.presheaf.stalk x) := by sorry
