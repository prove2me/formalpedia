-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom
-- name    : AlgebraicGeometry.RiemannForm.isConstScalar_tensorHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/dad96957-e840-5e9d-9ea3-e04cfaaeb6bf
-- title:
--   Constant scalars multiply under tensor product of module maps
-- statement:
--   Let $k$ be a field, let $A$ be a scheme (in the bottom universe), and let $f : A \to \operatorname{Spec} k$ be a morphism of schemes, where $k$ is regarded as a commutative ring via `CommRingCat.of`. For a module $M$ over $A$ (an object of `A.Modules`) and $c \in k$, the predicate `IsConstScalar f` says that an endomorphism $\sigma : M \to M$ acts on sections as multiplication by the constant $c$ pulled back along $f$: for every open $U \subseteq A$ and every section $s \in \Gamma(M, U)$ one has $\sigma_U(s) = a|_U \cdot s$, where $a \in \Gamma(A, \top)$ is the image of $c$ under the inverse of the isomorphism $k \cong \Gamma(\operatorname{Spec} k, \top)$ followed by the map on global sections $f^\sharp$, and $a|_U$ denotes its restriction along $U \le \top$. The theorem asserts: given modules $M, M'$ over $A$, endomorphisms $\sigma : M \to M$ and $\tau : M' \to M'$, and constants $c, c' \in k$ such that $\sigma$ acts as the constant scalar $c$ and $\tau$ as the constant scalar $c'$ in this sense, the tensor product morphism $\sigma \otimes_{\mathrm m} \tau$ on $M \otimes M'$, formed in the monoidal structure on `A.Modules`, acts as the constant scalar $c c'$.
--
--   This is the multiplicativity of constant-scalar actions under the monoidal product of modules on a scheme over a field. It is used in the study of Riemann forms and theta groups, where constants attached to endomorphisms of line bundles must be tracked through tensor products; among its consumers are the compatibility of constant scalars with whiskering, the multiplicativity of level pairing values under tensor isomorphisms, and the construction of monoid homomorphisms on theta groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_SheafOfModules_MonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.isConstScalar_tensorHom
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    {M M' : A.Modules} (σ : M ⟶ M) (τ : M' ⟶ M') (c c' : k)
    (hσ : IsConstScalar f σ c) (hτ : IsConstScalar f τ c') :
    IsConstScalar f (σ ⊗ₘ τ) (c * c') := by sorry
