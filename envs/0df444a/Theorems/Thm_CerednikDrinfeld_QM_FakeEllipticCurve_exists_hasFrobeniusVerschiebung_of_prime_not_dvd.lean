-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hasFrobeniusVerschiebung_of_prime_not_dvd
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_hasFrobeniusVerschiebung_of_prime_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/fae9a093-3fbb-59d3-8c75-319617b36629
-- title:
--   Existence of Frobenius twist and Verschiebung for fake elliptic curves
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, an algebraically closed field $k$, and a prime $\ell$ with $k$ of characteristic $\ell$, and assume $\ell \nmid N$. Let $E$ be a `FakeEllipticCurve Λ N k`: a scheme $E.A$ with a structure morphism $E.f$ to $\operatorname{Spec} k$ carrying a commutative relative group law, smooth and proper with connected fibres of topological Krull dimension $2$, together with an action of $\Lambda$ by endomorphisms of $E.A$ over $k$ which is unital, (anti)multiplicative, additive, a homomorphism for the group law and satisfies the trace condition on tangent spaces at geometric points, plus the level-$N$ data $E.C$, $E.\mathrm{lev}$. The conclusion asserts the existence of a second fake elliptic curve $E_\ell$ over $k$ of the same type such that `HasFrobeniusVerschiebung ℓ E Eℓ` holds, i.e. a `FrobeniusVerschiebungData` exists: a morphism $\mathrm{pr} : E_\ell.A \to E.A$ exhibiting $E_\ell.f$ as the pullback of $E.f$ along $\operatorname{Spec}$ of the $\ell$-power Frobenius of $k$ and compatible with the group laws, the $\Lambda$-actions and the level structures, morphisms $F : E.A \to E_\ell.A$ and $V : E_\ell.A \to E.A$ over $k$ which are homomorphisms for the relative group laws, commute with the $\Lambda$-actions and preserve the level structures, and the remaining compatibilities required by that structure.
--
--   This is the existence statement accompanying the definition of Frobenius–Verschiebung data for fake elliptic curves in characteristic $\ell$: the Frobenius twist $E^{(\ell)}$ of a fake elliptic curve, with its relative Frobenius and Verschiebung, exists whenever $\ell$ does not divide the level $N$. It is used in the comparison of the two legs of the Čerednik–Drinfeld setting over a residue field and in the bound on the number of torsion points of a fake elliptic curve in characteristic $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hasFrobeniusVerschiebung_of_prime_not_dvd.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_hasFrobeniusVerschiebung_of_prime_not_dvd
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (hℓN : ¬ ℓ ∣ N)
    (E : FakeEllipticCurve Λ N k) :
    ∃ Eℓ : FakeEllipticCurve Λ N k, FakeEllipticCurve.HasFrobeniusVerschiebung ℓ E Eℓ := by sorry
