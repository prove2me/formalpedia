-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_factorsThrough_iff_of_forall_geomPoint
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.factorsThrough_iff_of_forall_geomPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/ec6f5e15-6225-51d5-b6b3-ae3c00a17840
-- title:
--   Extra level at invertible ℓ determined by geometric points
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and a natural number $\ell$; let $S$ be a commutative ring in which the image of $\ell$ is a unit, and let $E$ be a fake elliptic curve datum of type $(\Lambda,N)$ over $S$: a morphism $f : A \to \operatorname{Spec} S$ which is smooth and proper with connected fibres of topological Krull dimension $2$, a commutative relative group law $L$ on the functor of points of $f$, an action of $\Lambda$ by $S$-endomorphisms of $A$ compatible with $L$ and satisfying the trace condition, together with the further data of the structure (a curve $C$ and the level map `E.lev` among them). Let $K$ and $K'$ be two extra levels at $\ell$ for $E$: each consists of a scheme with a closed immersion into $A$ whose sets of factoring $T$-points form, for every $S$-scheme $T$, a subgroup of $(A/S)(T)$ killed by $\ell$, stable under the $\Lambda$-action, meeting the points factoring through `E.lev` only in the identity, with structure morphism to $\operatorname{Spec} S$ finite, flat and locally of finite presentation of rank $\ell^2$ at every point, and with group of geometric points isomorphic to $\mathbb{Z}/\ell \times \mathbb{Z}/\ell$ over each algebraically closed field in which $\ell \neq 0$. Assume that for every algebraically closed field $k$, every ring homomorphism $s_k : S \to k$, and every $k$-point $Q$ of $A$ over $\operatorname{Spec}(s_k)$, the point $Q$ factors through the closed immersion of $K$ if and only if it factors through that of $K'$. Then for every scheme $T$, every $t : T \to \operatorname{Spec} S$ and every $Q : T \to A$ with $Q$ followed by $f$ equal to $t$, the morphism $Q$ factors through the closed immersion of $K$ if and only if it factors through that of $K'$, where factoring means the existence of a morphism from $T$ to the source whose composite with the closed immersion is $Q$.
--
--   This is the rigidity statement that an extra level structure at $\ell$, with $\ell$ invertible on the base, is determined by the geometric points it contains: two such subgroup schemes with the same geometric points have the same points with values in an arbitrary base scheme. It is used in the comparison of extra levels and in the fine and coarse moduli statements for the quaternionic moduli problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_factorsThrough_iff_of_forall_geomPoint.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.factorsThrough_iff_of_forall_geomPoint
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (ℓ : ℕ) (hℓ : ℓ.Prime)
    {S : Type} [CommRing S] (hℓS : IsUnit ((ℓ : ℕ) : S)) (E : FakeEllipticCurve Λ N S) (K K' : E.ExtraLevel ℓ)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) E.f),
      FactorsThrough K.levK Q ↔ FactorsThrough K'.levK Q)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t E.f) :
    FactorsThrough K.levK Q ↔ FactorsThrough K'.levK Q := by sorry
