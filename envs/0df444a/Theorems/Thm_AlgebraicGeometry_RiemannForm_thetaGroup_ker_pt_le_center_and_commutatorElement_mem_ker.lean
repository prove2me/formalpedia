-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_ker_pt_le_center_and_commutatorElement_mem_ker
-- name    : AlgebraicGeometry.RiemannForm.thetaGroup.ker_pt_le_center_and_commutatorElement_mem_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/92d41c12-0d74-5d43-ba21-27e800054c14
-- title:
--   Kernel of the theta group projection is central
-- statement:
--   Let $k$ be a type in the lowest universe carrying a field structure, assumed algebraically closed, let $A$ be a scheme (also in the lowest universe) and let $f : A \to \operatorname{Spec} k$ be a morphism. Let $L$ be a relative group law on $f$, that is, a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points of $A$ over each $t : T \to \operatorname{Spec} k$, with multiplication, unit and inversion satisfying associativity, the unit laws, left inversion and compatibility with base change along morphisms $\psi : T' \to T$ over $\operatorname{Spec} k$; let `hc` assert that this group law is commutative, and let `hA` assert that $f$ is smooth and proper, has connected fibres over every point of $\operatorname{Spec} k$, and admits some relative group law. Let $M$ be a module on $A$, assumed invertible in the sense that every point of $A$ has an open neighbourhood $U$ on which the pullback of $M$ along $U \hookrightarrow A$ is isomorphic to the unit sheaf of modules. The theta group $\mathrm{thetaGroup}\ f\ L\ hc\ M$ is the subgroup of $\operatorname{Aut}(A, M) \times (L.\mathrm{AlgPoints}\ hc\ k)^{\mathrm{mult}}$, the automorphism group being taken in the total category of the pullback fibration of modules, consisting of those pairs whose automorphism has base component the translation $\mathrm{translation}\ f\ L$ by the associated point, i.e. the map $A \to A$ obtained from $L$-multiplication of the identity point by the given constant point. The assertion is twofold: the kernel of the homomorphism $\mathrm{thetaGroup.pt}\ f\ L\ hc\ M$, which records the point component, is contained in the centre of the theta group, and for all $g, h$ in the theta group the commutator $\lbrack g, h \rbrack$ lies in that kernel.
--
--   This is the standard first structural fact about Mumford's theta group $\mathcal G(M)$ of an invertible sheaf on an abelian variety: it is a central extension of the group of translations preserving $M$ by the automorphisms of $M$ over the identity. It is used in the construction of the Weil pairing and level pairings attached to a polarisation, and in the splitting of theta groups over subgroups of two-torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_thetaGroup_ker_pt_le_center_and_commutatorElement_mem_ker.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_AlgebraicGeometry_ThetaGroup
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm
open scoped commutatorElement

theorem AlgebraicGeometry.RiemannForm.thetaGroup.ker_pt_le_center_and_commutatorElement_mem_ker
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) :
    (thetaGroup.pt f L hc M).ker ≤ Subgroup.center (thetaGroup f L hc M) ∧
    ∀ g h : thetaGroup f L hc M, ⁅g, h⁆ ∈ (thetaGroup.pt f L hc M).ker := by sorry
