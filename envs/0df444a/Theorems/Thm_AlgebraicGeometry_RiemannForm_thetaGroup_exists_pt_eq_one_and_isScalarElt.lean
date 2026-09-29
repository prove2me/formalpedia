-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_exists_pt_eq_one_and_isScalarElt
-- name    : AlgebraicGeometry.RiemannForm.thetaGroup.exists_pt_eq_one_and_isScalarElt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/def8098a-6a18-5b5c-8aae-9df89d538999
-- title:
--   Every non-zero scalar is realised in the theta group
-- statement:
--   Let $k$ be a field, let $A$ be a scheme and let $f : A \to \operatorname{Spec} k$ be a morphism equipped with a `RelativeGroupLaw` $L$, that is, a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$ of $T$-points over $\operatorname{Spec} k$, with multiplication, unit and inverse natural in $T$; assume $L$ is commutative (hypothesis `hc`). Let $M$ be an object of `A.Modules`, and let $c \in k$ with $c \neq 0$. The assertion is that there is an element $g$ of the theta group `thetaGroup f L hc M` — the subgroup of $\operatorname{Aut}(A, M) \times \mathrm{Multiplicative}(L.\mathrm{AlgPoints}\ hc\ k)$ consisting of pairs whose automorphism has underlying morphism of $A$ equal to translation by the given point — such that the point `thetaGroup.pt f L hc M g` is the trivial point, and `thetaGroup.IsScalarElt f L hc M g c` holds: for some witness of `pt g = 1`, the induced endomorphism `unitReading` of $M$ (the fibre component of $g$, composed with the canonical identifications of the pullback along the identity) is multiplication by the constant $c$, i.e. on every open $U$ and every section $s$ of $M$ over $U$ it is the action of the image of $c$ in $\Gamma(A, U)$ on $s$.
--
--   This is the statement that the scalars $k^\times$ are realised inside Mumford's theta group of $(A, M)$, namely as elements lying over the zero point and acting on $M$ by a constant homothety. It is used in the construction of a subgroup of the theta group of $M \otimes M$ whose points exhaust the $2$-torsion, in the treatment of polarisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_thetaGroup_exists_pt_eq_one_and_isScalarElt.lean

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

theorem AlgebraicGeometry.RiemannForm.thetaGroup.exists_pt_eq_one_and_isScalarElt
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (M : A.Modules) (c : k) (hc0 : c ≠ 0) :
    ∃ g : thetaGroup f L hc M, thetaGroup.pt f L hc M g = 1 ∧ thetaGroup.IsScalarElt f L hc M g c := by sorry
