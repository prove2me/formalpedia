-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_exists_sectionAt_eq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_exists_sectionAt_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/91b5cd07-e62a-5f57-8539-8a3e6eba2b5a
-- title:
--   Constant extra level from a homomorphism (ℤ/ℓ)² → A(S)
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a commutative ring $S$, a fake elliptic curve $E$ of type $(\Lambda,N)$ over $S$ — so in particular a scheme $E.A$ with a structure morphism $E.f$ to $\operatorname{Spec} S$, a commutative relative group law $E.L$, an action $E.\mathrm{act}$ of $\Lambda$ by $\operatorname{Spec} S$-endomorphisms, and a morphism $E.\mathrm{lev}$ from $E.C$ to $E.A$ — and a nonzero natural number $\ell$. Let $W$ assign to each $i \in (\mathbb{Z}/\ell)^2$ a section of $E.f$ over the identity of $\operatorname{Spec} S$, i.e. a morphism $\operatorname{Spec} S \to E.A$ splitting $E.f$. Assume: $W(i+j) = E.L.\mathrm{mul}$ applied to $W(i)$ and $W(j)$ for all $i,j$; for each $x \in \Lambda$ and each $i$, the section $W(i)$ followed by $E.\mathrm{act}\,x$ equals $W(j)$ for some $j$; for every algebraically closed field $k$ and every ring homomorphism $sk : S \to k$, the base changes $\mathrm{sectionAt}(W(i))$ along $\mathrm{geomPoint}\,k\,sk$ are pairwise distinct; and for every such $k, sk$, if $\mathrm{sectionAt}(W(i))$ factors through $E.\mathrm{lev}$ then $i = 0$. Then there is an extra level $K$ at $\ell$ on $E$ — a closed immersion $K.\mathrm{levK} : K.K \to E.A$ whose locus of factoring points contains the unit and is closed under $E.L$-multiplication and inversion, is killed by $\ell$, is stable under the $\Lambda$-action, meets $E.\mathrm{lev}$ only in the unit section, with $K.\mathrm{levK}$ followed by $E.f$ finite, flat and locally of finite presentation of fibre rank $\ell^2$, and with geometric fibres of order $\ell^2$ grouped as $(\mathbb{Z}/\ell)^2$ where $\ell \neq 0$ in $k$ — such that every $W(i)$ factors through $K.\mathrm{levK}$, and for every algebraically closed $k$, every $sk : S \to k$ and every point $Q$ of $E.f$ over $\mathrm{geomPoint}\,k\,sk$, the point $Q$ factors through $K.\mathrm{levK}$ if and only if $Q = \mathrm{sectionAt}(W(i))$ for some $i$.
--
--   This produces an extra level structure at $\ell$ on a fake elliptic curve over an arbitrary base from a constant family of $S$-valued sections forming a copy of $(\mathbb{Z}/\ell)^2$, separated at every geometric point and transversal to the given morphism $E.\mathrm{lev}$; the resulting $K$ is the disjoint union of $\ell^2$ copies of $\operatorname{Spec} S$ embedded by the sections $W(i)$. It is used in the construction and comparison of extra levels on fake elliptic curves, in particular in the criteria for such a level to be respected by an endomorphism and in the isomorphism statements for quaternionic moduli in the indefinite ramified case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_exists_sectionAt_eq.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_exists_sectionAt_eq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S) (ℓ : ℕ) [NeZero ℓ]
    (W : ZMod ℓ × ZMod ℓ → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f)
    (hW_add : ∀ i j : ZMod ℓ × ZMod ℓ, W (i + j) = E.L.mul (𝟙 (Spec (CommRingCat.of S))) (W i) (W j))
    (hW_stable : ∀ (x : ↥Λ) (i : ZMod ℓ × ZMod ℓ), ∃ j : ZMod ℓ × ZMod ℓ, pushPt (E.act x) (E.act_over x) (W i) = W j)
    (hW_inj : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (i j : ZMod ℓ × ZMod ℓ),
      FakeEllipticCurve.sectionAt (W i) k sk = FakeEllipticCurve.sectionAt (W j) k sk → i = j)
    (hW_lev : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (i : ZMod ℓ × ZMod ℓ),
      FactorsThrough E.lev (FakeEllipticCurve.sectionAt (W i) k sk) → i = 0) :
    ∃ K : E.ExtraLevel ℓ,
      (∀ i : ZMod ℓ × ZMod ℓ, FactorsThrough K.levK (W i)) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) E.f),
        FactorsThrough K.levK Q ↔ ∃ i : ZMod ℓ × ZMod ℓ, FakeEllipticCurve.sectionAt (W i) k sk = Q := by sorry
