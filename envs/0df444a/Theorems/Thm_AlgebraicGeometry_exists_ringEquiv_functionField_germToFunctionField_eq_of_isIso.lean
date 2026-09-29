-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_functionField_germToFunctionField_eq_of_isIso
-- name    : AlgebraicGeometry.exists_ringEquiv_functionField_germToFunctionField_eq_of_isIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/b104dd9c-2119-5c50-8160-c774b690d004
-- title:
--   Isomorphism of integral schemes induces germ-compatible function field isomorphism
-- statement:
--   Let $X$ and $Y$ be schemes (in a fixed universe) that are integral in Mathlib's sense, and let $f : X \to Y$ be a morphism which is an isomorphism. The assertion is that there exists a ring isomorphism $\iota : K(Y) \xrightarrow{\sim} K(X)$ between the function fields, i.e. between the stalks $\Gamma$-wise defined as `Y.functionField` and `X.functionField`, the stalks of the structure sheaves at the respective generic points, such that $\iota$ is compatible with germs at the generic points in the following sense: for every open subset $V \subseteq Y$ whose underlying scheme is non-empty and whose preimage $f^{-1}V \subseteq X$ also has non-empty underlying scheme (these non-emptiness assumptions being exactly what makes the germ maps into the function fields available), and for every section $t \in \Gamma(Y, V)$, one has $$\iota\bigl(\mathrm{germ}_{V}(t)\bigr) = \mathrm{germ}_{f^{-1}V}\bigl(f^{\ast}t\bigr),$$ where $\mathrm{germ}$ denotes `Scheme.germToFunctionField`, the map sending a section to its germ at the generic point, and $f^{\ast}t =$ `f.app V t` is the pullback of $t$ along $f$. Thus the existence statement packages both the ring isomorphism of function fields and its characterisation on germs of sections over all such opens.
--
--   This is the standard fact that an isomorphism of integral schemes identifies their function fields, in the form of a concrete germ-level identity rather than merely an abstract isomorphism; the germ formulation is what allows it to be combined with sheaf-theoretic data downstream. It is used in the construction of Galois frames for Čerednik–Drinfeld moduli towers, where function fields of integral models are compared along isomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_ringEquiv_functionField_germToFunctionField_eq_of_isIso.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_ringEquiv_functionField_germToFunctionField_eq_of_isIso
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsIso f] :
    ∃ ι : Y.functionField ≃+* X.functionField,
      ∀ (V : Y.Opens) [Nonempty (V : Scheme.{u})] [Nonempty ((f ⁻¹ᵁ V : X.Opens) : Scheme.{u})] (t : Γ(Y, V)),
        ι (Y.germToFunctionField V t) = X.germToFunctionField (f ⁻¹ᵁ V) (f.app V t) := by sorry
