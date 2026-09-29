-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_existsUnique_isConstScalar
-- name    : AlgebraicGeometry.RiemannForm.existsUnique_isConstScalar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/e56830d0-92d9-50c2-a8d6-beefa338b33d
-- title:
--   Endomorphisms of an invertible module are unique constant scalars
-- statement:
--   Let $k$ be a field, let $A$ be a scheme (in universe $0$) and let $f : A \to \operatorname{Spec} k$ be a morphism of schemes satisfying `AbelianSchemePropertyBundle k f`, that is: $f$ is smooth, $f$ is proper, for every point $s$ of $\operatorname{Spec} k$ the fibre $f^{-1}(s)$ of the underlying continuous map is connected, and the set of relative group laws on $f$ is nonempty (a relative group law being a functorial group structure, with multiplication, unit and inverse satisfying associativity, unit and inverse laws and compatible with base change, on the sets of $A$-valued points over $\operatorname{Spec} k$ of arbitrary $k$-schemes $T$). Let $M$ be a sheaf of modules on $A$ which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ such that the pullback of $M$ along the inclusion $U \hookrightarrow A$ is isomorphic to the unit module on $U$, and let $\sigma : M \to M$ be an endomorphism of $M$. Then there is exactly one $c \in k$ which `IsConstScalar f σ c`, i.e. such that for every open $U \subseteq A$ and every section $s \in \Gamma(M, U)$ one has $\sigma_U(s) = \bigl(f^{\sharp}(c)|_U\bigr) \cdot s$, where $f^{\sharp}(c) \in \Gamma(A, \mathcal{O}_A)$ is the image of $c$ under the map on global sections induced by $f$ and the canonical isomorphism $k \cong \Gamma(\operatorname{Spec} k, \mathcal{O})$, restricted from $\top$ to $U$.
--
--   This is the standard rigidity statement that an endomorphism of a line bundle on an abelian variety is multiplication by a scalar, resting on $\Gamma(A, \mathcal{O}_A) = k$ for $A$ proper, connected and reduced over $k$; the cited input is the identification of global functions on $A$ with constants. It is used in the construction of Riemann forms and level pairings, in the criterion for a pullback of a translation to be trivial, and in the analysis of scalar elements of the theta group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_existsUnique_isConstScalar.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.existsUnique_isConstScalar
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (hA : AbelianSchemePropertyBundle k f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) (σ : M ⟶ M) :
    ∃! c : k, IsConstScalar f σ c := by sorry
