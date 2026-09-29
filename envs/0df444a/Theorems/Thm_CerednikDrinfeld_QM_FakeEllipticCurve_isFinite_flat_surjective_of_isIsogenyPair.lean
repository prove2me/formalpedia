-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_flat_surjective_of_isIsogenyPair
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_flat_surjective_of_isIsogenyPair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/8dd54b69-26de-5ccf-80eb-db1a10e9362a
-- title:
--   Isogeny pairs of fake elliptic curves: finite, flat, surjective
-- statement:
--   Let $a,b\in\mathbb{Q}$, let $\Lambda$ be a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ containing the image of every integer $m$ under $\mathbb{Z}\to\mathbb{Q}\to\mathbb{H}[\mathbb{Q},a,b]$, let $N$ be a natural number, let $r$ be a prime and $d$ a natural number, and let $S$ be a commutative ring. Let $E$ and $A$ be fake elliptic curves over $S$ for the data $(\Lambda,N)$, that is, each consists of a scheme with a structure morphism to $\operatorname{Spec} S$ carrying a commutative relative group law on its functor of points, which is smooth and proper with connected fibres and has all fibres of topological Krull dimension $2$, together with an action of $\Lambda$ by endomorphisms over $\operatorname{Spec} S$ that is additive and multiplicative, respects the group law, and satisfies a trace condition on the tangent space at an algebraically closed geometric point, plus further auxiliary data. Let $\varphi : E.A \to A.A$ and $\varphi' : A.A \to E.A$ be morphisms of schemes forming an isogeny pair of degree $r^d$, i.e. both are morphisms over $\operatorname{Spec} S$, both are homomorphisms for the relative group laws on $T$-points for every $S$-scheme $T$, both commute with the $\Lambda$-actions ($E.\mathrm{act}\,x$ followed by $\varphi$ equals $\varphi$ followed by $A.\mathrm{act}\,x$, and symmetrically for $\varphi'$), and, whenever the image of $r^d$ in $\mathbb{H}[\mathbb{Q},a,b]$ lies in $\Lambda$, $\varphi$ followed by $\varphi'$ equals the action of $r^d$ on $E$ and $\varphi'$ followed by $\varphi$ equals the action of $r^d$ on $A$. Then $\varphi$ is finite, flat, locally of finite presentation and surjective.
--
--   This is the standard fact that an isogeny of abelian schemes is finite, faithfully flat and locally of finite presentation, in the form needed for fake elliptic curves with quaternionic multiplication; the hypothesis on $\Lambda$ makes the condition $\varphi\varphi'=[r^d]$ effective. It is what makes the degree (the rank of the associated finite locally free module) of an isogeny available, and it is used in the rigidification lemmas for correspondences and degree windows on fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_flat_surjective_of_isIsogenyPair.lean

import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_QMRigidification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_flat_surjective_of_isIsogenyPair
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (r d : ℕ) [Fact r.Prime] (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ A.A) (φ' : A.A ⟶ E.A) (h : FakeEllipticCurve.IsIsogenyPair (r ^ d) E A φ φ') :
    IsFinite φ ∧ Flat φ ∧ LocallyOfFinitePresentation φ ∧ Surjective φ := by sorry
