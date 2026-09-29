-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_tensor_self_pt_eq_and_isScalarElt_mul_self
-- name    : AlgebraicGeometry.RiemannForm.thetaGroup.exists_monoidHom_tensor_self_pt_eq_and_isScalarElt_mul_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/e61af3df-3343-5f1c-98a9-4bb5e2a6f438
-- title:
--   Tensor-square homomorphism of theta groups doubles scalars
-- statement:
--   Let $k$ be a field, $A$ a scheme over $\operatorname{Spec} k$ via $f : A \to \operatorname{Spec} k$, and let $L$ be a relative group law for $f$, that is, a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} k$, with multiplication, unit and inverse natural in $T$; assume $L$ is commutative ($hc$), and that $f$ satisfies the bundle of abelian-scheme properties $hA$ (smooth, proper, connected fibres, and admitting a relative group law). Let $M$ be a module object on $A$ which is invertible ($hM$: every point has a neighbourhood $U$ on which the pullback of $M$ along $U \hookrightarrow A$ is isomorphic to the unit module). Here $\mathrm{thetaGroup}\ f\ L\ hc\ N$ is the subgroup of $\operatorname{Aut}(A, N) \times \mathrm{Multiplicative}(L.\mathrm{AlgPoints}\ hc\ k)$ consisting of pairs whose automorphism has base equal to translation by the corresponding point, and $\mathrm{pt}$ is its point component. The assertion is that there exists a monoid homomorphism $\varepsilon : \mathrm{thetaGroup}\ f\ L\ hc\ M \to \mathrm{thetaGroup}\ f\ L\ hc\ (M \otimes M)$ such that $\mathrm{pt}(\varepsilon g) = \mathrm{pt}(g)$ for every $g$, and such that whenever $g$ is a scalar element with value $c \in k$ — meaning $\mathrm{pt}(g) = 1$ and the induced endomorphism of $M$ is multiplication by the constant $c$ — then $\varepsilon g$ is a scalar element of $\mathrm{thetaGroup}\ f\ L\ hc\ (M \otimes M)$ with value $c \cdot c$.
--
--   This is the functoriality of the theta group under tensor squaring: the map $\mathcal G(M) \to \mathcal G(M \otimes M)$ lies over the identity on points and sends a central scalar $c$ to $c^2$, in the spirit of Mumford's analysis of $e^L$. It feeds the commutation statement [`AlgebraicGeometry.RiemannForm.thetaGroup.mul_comm_of_two_torsion_of_forall_two_torsion_pullback_translation_iso`](thm.html#AlgebraicGeometry.RiemannForm.thetaGroup.mul_comm_of_two_torsion_of_forall_two_torsion_pullback_translation_iso), where it reduces commutativity on $2$-torsion to group theory in the theta group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_thetaGroup_exists_monoidHom_tensor_self_pt_eq_and_isScalarElt_mul_self.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ThetaGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.thetaGroup.exists_monoidHom_tensor_self_pt_eq_and_isScalarElt_mul_self
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) :
    ∃ ε : thetaGroup f L hc M →* thetaGroup f L hc (M ⊗ M),
      (∀ g : thetaGroup f L hc M, thetaGroup.pt f L hc (M ⊗ M) (ε g) = thetaGroup.pt f L hc M g) ∧
      (∀ (g : thetaGroup f L hc M) (c : k), thetaGroup.IsScalarElt f L hc M g c →
        thetaGroup.IsScalarElt f L hc (M ⊗ M) (ε g) (c * c)) := by sorry
