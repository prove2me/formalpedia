-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_existsUnique_isScalarElt_and_isScalarElt_mul
-- name    : AlgebraicGeometry.RiemannForm.thetaGroup.existsUnique_isScalarElt_and_isScalarElt_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/2b45aa6d-699f-5fc3-a152-d974e02ec76b
-- title:
--   Theta-group elements over the origin act by unique scalars
-- statement:
--   Let $k$ be an algebraically closed field, let $f : A \to \operatorname{Spec} k$ be a morphism of schemes, let $L$ be a relative group law on $f$ (a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $k$, for all schemes $T \to \operatorname{Spec} k$), let $hc$ assert that $L$ is commutative on every such set of $T$-points, and let $hA$ be the bundle of properties asserting that $f$ is smooth, proper, has connected fibres over every point of $\operatorname{Spec} k$, and admits a relative group law. Let $M$ be a sheaf of modules on $A$ which is invertible, i.e. every point of $A$ has an open neighbourhood $U$ such that the pullback of $M$ along $U \hookrightarrow A$ is isomorphic to the unit sheaf of modules on $U$. Here $\mathcal{G} =$ `thetaGroup f L hc M` is the subgroup of $\operatorname{Aut}(A, M) \times (L.\mathrm{AlgPoints}\ hc\ k)^{\times}$ (automorphisms of the pair consisting of $A$ and $M$, paired with points written multiplicatively) consisting of those pairs whose automorphism has underlying morphism of $A$ equal to translation by the given point; `thetaGroup.pt` records that point, so that $\mathrm{pt}(g) = 1$ says that $g$ lies over the origin and hence induces, via the unit coherence of pullback, an endomorphism of $M$. The predicate `IsScalarElt f L hc M g c` says that $\mathrm{pt}(g) = 1$ and that this induced endomorphism $\sigma$ of $M$ is multiplication by the constant $c \in k$: for every open $U \subseteq A$ and every section $s$ of $M$ over $U$, $\sigma(s)$ equals the restriction to $U$ of the global function on $A$ obtained from $c$, acting on $s$. The theorem asserts four statements simultaneously: first, for every $g \in \mathcal{G}$ with $\mathrm{pt}(g) = 1$ there is a unique $c \in k$ with `IsScalarElt` holding for $g$ and $c$; second, if $g$ acts by $c$ and $h$ acts by $d$ then $gh$ acts by $cd$; third, the identity of $\mathcal{G}$ acts by $1 \in k$; fourth, if $g, h \in \mathcal{G}$ satisfy $\mathrm{pt}(g) = \mathrm{pt}(h)$ then $\mathrm{pt}(g^{-1}h) = 1$.
--
--   This is the basic structural fact about the theta group (Heisenberg group) of an invertible sheaf on an abelian variety: the elements lying over the origin form a copy of $k^{\times}$ sitting centrally in $\mathcal{G}$, acting on $M$ by constants, and two lifts of the same point differ by such an element. It is used in the construction of the commutator pairing and the associated level pairings on torsion points, and in the analysis of theta groups of polarisations and of $M \otimes M$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_thetaGroup_existsUnique_isScalarElt_and_isScalarElt_mul.lean

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

theorem AlgebraicGeometry.RiemannForm.thetaGroup.existsUnique_isScalarElt_and_isScalarElt_mul
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) :
    (∀ g : thetaGroup f L hc M, thetaGroup.pt f L hc M g = 1 → ∃! c : k, thetaGroup.IsScalarElt f L hc M g c) ∧
    (∀ (g h : thetaGroup f L hc M) (c d : k), thetaGroup.IsScalarElt f L hc M g c →
      thetaGroup.IsScalarElt f L hc M h d → thetaGroup.IsScalarElt f L hc M (g * h) (c * d)) ∧
    thetaGroup.IsScalarElt f L hc M 1 1 ∧
    (∀ g h : thetaGroup f L hc M, thetaGroup.pt f L hc M g = thetaGroup.pt f L hc M h →
      thetaGroup.pt f L hc M (g⁻¹ * h) = 1) := by sorry
