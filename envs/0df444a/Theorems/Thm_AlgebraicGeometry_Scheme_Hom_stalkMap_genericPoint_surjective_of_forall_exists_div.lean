-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_stalkMap_genericPoint_surjective_of_forall_exists_div
-- name    : AlgebraicGeometry.Scheme.Hom.stalkMap_genericPoint_surjective_of_forall_exists_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/c2a90509-b5e7-57a9-91ef-420c94dabaf9
-- title:
--   Surjectivity at the generic point from quotients of pulled-back sections
-- statement:
--   Let $Y$ and $Z$ be schemes with $Y$ integral, let $f : Y \to Z$ be a morphism of schemes, let $V$ be an open subscheme of $Z$, and write $\eta$ for the generic point of $Y$; assume $f(\eta) \in V$, so that $\eta$ lies in the open preimage $f^{-1}V$. The hypothesis is that every element $x$ of the function field of $Y$, i.e. of the stalk $\mathcal{O}_{Y,\eta}$, admits sections $a, b \in \Gamma(Z, V)$ such that the germ at $\eta$ of the pull-back $f^{\#}_V(b) \in \Gamma(Y, f^{-1}V)$ is non-zero and $x \cdot (f^{\#}_V b)_\eta = (f^{\#}_V a)_\eta$ in $\mathcal{O}_{Y,\eta}$; that is, $x$ is the quotient of the germs of the pull-backs of $a$ and $b$. The conclusion is that the stalk map $f^{\#}_\eta : \mathcal{O}_{Z, f(\eta)} \to \mathcal{O}_{Y,\eta}$ induced by $f$ at $\eta$ is a surjective function. No reducedness or other hypothesis is imposed on $Z$, and $V$ is not assumed affine.
--
--   This is the surjectivity half of a birationality test at the generic point: a morphism from an integral scheme whose pulled-back sections over one open set $V \ni f(\eta)$ generate the whole function field by quotients induces a surjection on stalks at $\eta$. It is used by [`AlgebraicGeometry.Scheme.Hom.isIso_stalkMap_genericPoint_of_isReduced_of_forall_specializes_of_forall_exists_div`](thm.html#AlgebraicGeometry.Scheme.Hom.isIso_stalkMap_genericPoint_of_isReduced_of_forall_specializes_of_forall_exists_div), where it is combined with conditions forcing $\mathcal{O}_{Z,f(\eta)}$ to be a field to conclude that the stalk map is an isomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_stalkMap_genericPoint_surjective_of_forall_exists_div.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.stalkMap_genericPoint_surjective_of_forall_exists_div
    {Y Z : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ Z) (V : Z.Opens) (hV : f (genericPoint Y) ∈ V)
    (hgen : ∀ x : Y.functionField, ∃ a b : Γ(Z, V),
      Y.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Y) hV (f.app V b) ≠ 0 ∧
        x * Y.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Y) hV (f.app V b) =
          Y.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Y) hV (f.app V a)) :
    Function.Surjective (f.stalkMap (genericPoint Y)) := by sorry
