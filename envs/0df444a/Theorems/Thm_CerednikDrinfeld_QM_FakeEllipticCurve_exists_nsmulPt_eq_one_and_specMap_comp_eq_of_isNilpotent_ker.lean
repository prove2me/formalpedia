-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_nsmulPt_eq_one_and_specMap_comp_eq_of_isNilpotent_ker
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_nsmulPt_eq_one_and_specMap_comp_eq_of_isNilpotent_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/bae7e81a-f154-5044-993d-61e528b9dce3
-- title:
--   Lifting m-torsion points across nilpotent thickenings
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and commutative rings $S$, $S_0$. Let $E$ be a fake elliptic curve of type $(\Lambda,N)$ over $S$: a scheme $A$ with a structure morphism $f : A \to \operatorname{Spec} S$, a relative group law $L$ on $f$ (functorial multiplication, unit and inverse on $S$-points, associative, unital, with inverses, and compatible with base change) which is commutative, together with smoothness, properness, connectedness of fibres and existence of a group law, all fibres of topological Krull dimension $2$, an action of $\Lambda$ on $A$ over $S$ that is multiplicative, additive on points and satisfies a trace condition on tangent spaces at geometric points, and further data including a curve $C$ and the level-$N$ structure. Let $m$ be a natural number whose image in $S$ is a unit, and let $p : S \to S_0$ be a surjective ring homomorphism whose kernel is a nilpotent ideal. Let $P_0$ be a point of $A$ over the morphism $\operatorname{Spec} p : \operatorname{Spec} S_0 \to \operatorname{Spec} S$, that is, a morphism $\operatorname{Spec} S_0 \to A$ whose composite with $f$ is $\operatorname{Spec} p$, and suppose $P_0$ is $m$-torsion, in the sense that the $m$-fold iterate of $L$-multiplication by $P_0$ starting from the unit (the recursion $0 \mapsto$ unit, $n+1 \mapsto \text{mul}(n\text{-fold}, P_0)$) equals the unit point over $\operatorname{Spec} p$. The conclusion is that there exists a section $P$ of $f$ over the identity of $\operatorname{Spec} S$, that is, a morphism $\operatorname{Spec} S \to A$ splitting $f$, which is again $m$-torsion for $L$ and whose restriction along $\operatorname{Spec} p$, namely $\operatorname{Spec} p$ followed by $P$, equals $P_0$.
--
--   This is the existence half of the infinitesimal lifting property for $m$-torsion sections when $m$ is invertible on the base: since the $m$-kernel of $L$ is then finite étale over $S$, points of it extend across nilpotent thickenings of the base. It is used in establishing that full level structures on fake elliptic curves extend along such thickenings, via [`CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_comp_eq_specMap_comp_of_isNilpotent_ker`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_comp_eq_specMap_comp_of_isNilpotent_ker), and it invokes [`CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_nsmulPt_eq_one_and_specMap_comp_eq_of_isNilpotent_ker.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_nsmulPt_eq_one_and_specMap_comp_eq_of_isNilpotent_ker
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S₀ : Type} [CommRing S] [CommRing S₀] (E : FakeEllipticCurve Λ N S)
    (m : ℕ) (hm : IsUnit ((m : ℕ) : S))
    (p : S →+* S₀) (hp : Function.Surjective p) (hI : IsNilpotent (RingHom.ker p))
    (P₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom p)) E.f)
    (hP₀ : nsmulPt E.L (Spec.map (CommRingCat.ofHom p)) m P₀ = E.L.one (Spec.map (CommRingCat.ofHom p))) :
    ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f,
      nsmulPt E.L (𝟙 (Spec (CommRingCat.of S))) m P = E.L.one (𝟙 (Spec (CommRingCat.of S))) ∧
      Spec.map (CommRingCat.ofHom p) ≫ P.1 = P₀.1 := by sorry
