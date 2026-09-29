-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isPullbackVia_id
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/dc46587c-d28a-5827-9b7d-8677330ba901
-- title:
--   Reflexivity: a fake elliptic curve is its own base change along id_S
-- statement:
--   Let $a,b$ be rationals, let $\Lambda$ be a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, let $N$ be a natural number, let $S$ be a commutative ring, and let $E$ be a fake elliptic curve of type $(\Lambda,N)$ over $S$, i.e. a structure consisting of a scheme $E.A$ with a structure morphism $E.f : E.A \to \operatorname{Spec} S$ carrying a commutative relative group law $E.L$ on its functor of points, the abelian-scheme property bundle, two-dimensional fibres, a $\Lambda$-action $E.\mathrm{act}$ by endomorphisms over $S$ satisfying the listed multiplicativity, additivity and trace conditions, together with the level datum $E.C \to E.A$ and the remaining fields. Then `FakeEllipticCurve.IsPullbackVia` holds for the identity ring homomorphism of $S$, for $E$ in both slots, and for the identity morphism $\mathbb{1}_{E.A}$: the square formed by $\mathbb{1}_{E.A}$, $E.f$, $E.f$ and $\operatorname{Spec}(\mathrm{id}_S)$ is a pullback; composition with $\mathbb{1}_{E.A}$ takes the group-law product of any two $T$-points over any $t' : T \to \operatorname{Spec} S$ to the product of their images over $t' \circ \operatorname{Spec}(\mathrm{id}_S)$; $\mathbb{1}_{E.A}$ commutes with $E.\mathrm{act}\,x$ for every $x \in \Lambda$; and every $T$-point factoring through $E.\mathrm{lev}$ still factors through $E.\mathrm{lev}$ after composition with $\mathbb{1}_{E.A}$.
--
--   This is the reflexivity of the base-change (pullback) relation on the moduli groupoids of fake elliptic curves with $\Lambda$-action and level structure: the identity morphism exhibits $E$ as the base change of itself along $\mathrm{id}_S$. It is used throughout the construction of the moduli functor, for instance in the uniqueness of full level structures under norm-level transport and in the rigidification results producing pullbacks along ring maps with nilpotent kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isPullbackVia_id.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isPullbackVia_id
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S) :
    FakeEllipticCurve.IsPullbackVia (RingHom.id S) E E (𝟙 E.A) := by sorry
