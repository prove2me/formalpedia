-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_mapPt_negMor_mul
-- name    : AlgebraicGeometry.Polarisation.mapPt_negMor_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/0245967f-b67e-5f1a-b298-fca22bc9e4e9
-- title:
--   Inversion respects a commutative relative group law on points
-- statement:
--   Let $R$ be a commutative ring, let $A$ be a scheme and let $f : A \to \operatorname{Spec} R$ be a morphism equipped with a relative group law $L$, i.e. a functorial group structure on the sets $\mathrm{SchemeHomOver}\,t\,f = \{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$ of $T$-points over $\operatorname{Spec} R$, given by operations `mul`, `one`, `inv` satisfying associativity, the unit laws, left inversion and naturality of `mul` under base change of the test object. Assume $L$ is commutative, in the sense that `mul t x y = mul t y x` for all test morphisms $t$ and all points $x,y$. Write $[-1] =$ `Polarisation.negMor f L` for the underlying morphism $A \to A$ of the $L$-inverse of the tautological point $\mathrm{id}_A$ of $A$ over $f$, together with the identity `Polarisation.negMor_over` expressing that $[-1]$ followed by $f$ equals $f$. Then for every test scheme $T$ with structure morphism $t : T \to \operatorname{Spec} R$ and all $T$-points $P, Q$ of $A$ over $t$, post-composition with $[-1]$ (the operation [`CerednikDrinfeld.QM.mapPt`](def/CerednikDrinfeld_QMModuli.html#L28), $P \mapsto P$ followed by $[-1]$) satisfies $(P \cdot Q) \circ [-1] = (P \circ [-1]) \cdot (Q \circ [-1])$, the products being taken with `L.mul t`.
--
--   This is the statement that the inversion morphism $[-1]$ of a commutative relative group law is a homomorphism on $T$-points, in the form needed when $[-1]$ is fed to results that require a morphism compatible with the group law. It is used in the comparison of theta-group level pairings under $[-1]$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_mapPt_negMor_mul.lean

import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.Polarisation.mapPt_negMor_mul
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f) :
    CerednikDrinfeld.QM.mapPt (Polarisation.negMor f L) (Polarisation.negMor_over f L) (L.mul t P Q) =
      L.mul t (CerednikDrinfeld.QM.mapPt (Polarisation.negMor f L) (Polarisation.negMor_over f L) P)
        (CerednikDrinfeld.QM.mapPt (Polarisation.negMor f L) (Polarisation.negMor_over f L) Q) := by sorry
