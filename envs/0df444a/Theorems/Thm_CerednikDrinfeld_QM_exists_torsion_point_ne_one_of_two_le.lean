-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_torsion_point_ne_one_of_two_le
-- name    : CerednikDrinfeld.QM.exists_torsion_point_ne_one_of_two_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/c5596c88-3ce9-5b91-823d-808fcecb651f
-- title:
--   Existence of a non-trivial n-torsion point, n≥ 2
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$ a morphism, and let $L$ be a relative group law for $f$: for every scheme $T$ and every $t : T \to \operatorname{Spec} k$ it equips the set of $t$-sections $\{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$ with a multiplication, a unit and an inverse satisfying associativity, the two unit laws and left inversion, the multiplication being compatible with base change along any $\psi : T' \to T$ over $\operatorname{Spec} k$. Assume $L$ is commutative, i.e. the multiplication on each set of $t$-sections is commutative, and assume the bundle `AbelianSchemePropertyBundle` for $f$, namely that $f$ is smooth and proper, that every fibre $f^{-1}(s)$ is connected, and that a relative group law for $f$ exists. Let $g$ be a natural number such that each fibre of $f$ over a point of $\operatorname{Spec} k$ has topological Krull dimension $g$, with $1 \le g$, and let $n \ge 2$. Then there are a commutative ring $R$, a morphism $t : \operatorname{Spec} R \to \operatorname{Spec} k$ and a $t$-section $x$ of $f$ such that the $n$-fold iterated product of $x$ (defined by recursion from the unit) equals the unit section $L.\mathrm{one}\ t$, while $x$ itself differs from the unit section.
--
--   This is the statement that a positive-dimensional abelian scheme over an algebraically closed field has a non-trivial $n$-torsion point for $n \ge 2$, phrased with test rings rather than $k$-points so as to be valid in all characteristics (the $n$-torsion may be non-étale). It is used in the study of polarisations, where it feeds the argument that the kernel of a suitable line bundle cannot be trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_torsion_point_ne_one_of_two_le.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm AlgebraicGeometry.Polarisation CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.exists_torsion_point_ne_one_of_two_le
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g) (hg : 1 ≤ g)
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ (R : Type) (_ : CommRing R) (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      L.nsmul t n x = L.one t ∧ x ≠ L.one t := by sorry
