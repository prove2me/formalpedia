-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_exists_addSubgroup_mem_iff_nonempty_pullback_translation_iso
-- name    : AlgebraicGeometry.RiemannForm.exists_addSubgroup_mem_iff_nonempty_pullback_translation_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/d4628b4f-a68c-5a02-8b8f-e415984dc502
-- title:
--   Stabiliser of a module under translations is a subgroup
-- statement:
--   Let $k$ be a field, let $A$ be a scheme and $f : A \to \operatorname{Spec}(k)$ a morphism, and let $L$ be a relative group law for $f$: for every scheme $T$ and every $t : T \to \operatorname{Spec}(k)$ a multiplication, unit and inverse on the set $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points of $A$ over $t$, satisfying associativity, the unit laws and left inverse law, with multiplication natural in $T$ along morphisms $\psi : T' \to T$ over $\operatorname{Spec}(k)$. Assume $hc$, that all these multiplications are commutative, and let $\mathcal L$ be an object of $A$-modules. Write $L.\mathrm{AlgPoints}\ hc\ k$ for the additive group obtained from the $k$-points, i.e. the sections $\varphi : \operatorname{Spec}(k) \to A$ with $\varphi \circ f = \operatorname{Spec}$ of the structure map $k \to k$, and for such a point $Q$ let $T_Q = \mathrm{translation}\ f\ L\ Q$ be the endomorphism of $A$ given by the first component of the product, under $L$ over $f$, of the identity point $\mathrm{id}_A$ with the constant point at $Q$. The assertion is that there is an additive subgroup $H$ of $L.\mathrm{AlgPoints}\ hc\ k$ such that for every $Q$, one has $Q \in H$ if and only if the type of isomorphisms $T_Q^{*}\mathcal L \cong \mathcal L$ of $A$-modules is nonempty, where $T_Q^{*}$ denotes `Scheme.Modules.pullback` along $T_Q$.
--
--   This is the statement that the stabiliser $K(\mathcal L)(k) = \{Q \mid T_Q^{*}\mathcal L \cong \mathcal L\}$ of a module under translations is a subgroup of the group of $k$-points, in the style of Mumford's subgroup $K(L)$ attached to a line bundle on an abelian variety; here no hypothesis is placed on $\mathcal L$ or on $A$ beyond the commutative relative group law. It is used in the study of Riemann forms and Euler characteristics, in particular by the results on finiteness of this stabiliser under finiteness of torsion, on its being everything when all points are torsion, and in the divisibility statement for Euler characteristics.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_exists_addSubgroup_mem_iff_nonempty_pullback_translation_iso.lean

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

theorem AlgebraicGeometry.RiemannForm.exists_addSubgroup_mem_iff_nonempty_pullback_translation_iso
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (𝓛 : A.Modules) :
    ∃ H : AddSubgroup (L.AlgPoints hc k), ∀ Q : L.AlgPoints hc k,
      Q ∈ H ↔ Nonempty ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).obj 𝓛 ≅ 𝓛) := by sorry
