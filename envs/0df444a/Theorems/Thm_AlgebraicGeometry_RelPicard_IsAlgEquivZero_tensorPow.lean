-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_tensorPow
-- name    : AlgebraicGeometry.RelPicard.IsAlgEquivZero.tensorPow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/4460d7c4-1f07-59df-90d0-e43734baea72
-- title:
--   Tensor powers preserve algebraic equivalence to zero
-- statement:
--   Let $k$ be a field, let $A$ be a scheme with a morphism $a : A \to \operatorname{Spec} k$, and let $L$ be an object of $A$.`Modules`. Assume `IsAlgEquivZero a L`, that is: there are a scheme $T'$ and a morphism $h : T' \to \operatorname{Spec} k$ that is locally of finite type and geometrically integral, a module $M$ on the fibre product $A \times_{\operatorname{Spec} k} T'$ which is invertible in the sense that every point of that scheme has an open neighbourhood $U$ whose restriction of $M$ along the inclusion $U.\iota$ is isomorphic to the unit sheaf of modules on $U$, together with two sections $t_0, t_1$ of $h$ over the identity of $\operatorname{Spec} k$ (morphisms $\operatorname{Spec} k \to T'$ whose composite with $h$ is the identity), such that the pullback of $M$ along the induced map $A \times_{\operatorname{Spec} k} \operatorname{Spec} k \to A \times_{\operatorname{Spec} k} T'$ attached to $t_0$ is isomorphic to the unit module on $A \times_{\operatorname{Spec} k} \operatorname{Spec} k$ (the product taken along the identity), and the pullback along the map attached to $t_1$ is isomorphic to the pullback of $L$ along the first projection. Then for every natural number $n$ the same predicate holds for $L$.`tensorPow` $n$, where the tensor power is defined by $L^{\otimes 0} = \mathbb{1}$, the monoidal unit of $A$.`Modules`, and $L^{\otimes (n+1)} = L^{\otimes n} \otimes L$.
--
--   This is the statement that the line bundles (more generally, modules) algebraically equivalent to zero on a $k$-scheme are stable under iterated tensor product, i.e. that $\operatorname{Pic}^0$ is closed under the $n$-th power map. It is used in the verification that a bundle whose pullback is isomorphic to a tensor power of the Poincaré bundle is fibrewise algebraically equivalent to zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_tensorPow.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.IsAlgEquivZero.tensorPow
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)} {L : A.Modules}
    (hL : IsAlgEquivZero a L) (n : ℕ) : IsAlgEquivZero a (L.tensorPow n) := by sorry
