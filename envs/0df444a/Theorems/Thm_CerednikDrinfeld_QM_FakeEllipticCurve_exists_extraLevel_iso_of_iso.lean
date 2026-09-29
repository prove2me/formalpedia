-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_iso_of_iso
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_iso_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/07ed43f8-4609-5f5d-9c34-14b34311f842
-- title:
--   Transport of extra level ℓ structures along isomorphisms
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a commutative ring $S$ and a natural number $\ell$. Let $E$ and $E'$ be fake elliptic curves of level $N$ over $S$ for $\Lambda$, i.e. objects of `FakeEllipticCurve Λ N S`, each consisting of a scheme over $\operatorname{Spec} S$ carrying a commutative relative group law, a property bundle making it an abelian scheme with two-dimensional fibres, an action of $\Lambda$ by endomorphisms over the base which is additive and multiplicative and whose traces on tangent spaces are prescribed by reduced traces, together with a level-$N$ datum `lev`. Assume `FakeEllipticCurve.Iso E' E`, that is, there is an isomorphism $e : E'.A \cong E.A$ of the underlying schemes commuting with the structure morphisms to $\operatorname{Spec} S$, compatible with the group laws on $T$-points for every test scheme $T$, commuting with the $\Lambda$-actions, and such that a $T$-point factors through $E'.\mathrm{lev}$ if and only if its image factors through $E.\mathrm{lev}$. Let $K'$ be an extra level at $\ell$ on $E'$: a closed immersion into $E'.A$ whose $T$-points form a subgroup of the $T$-points of $E'$ that is killed by $\ell$, stable under $\Lambda$, meets the level-$N$ datum only in the identity, and is finite, flat and locally of finite presentation over $S$ of rank $\ell^2$, with geometric fibres isomorphic as groups to $(\mathbb{Z}/\ell)^2$ whenever $\ell$ is invertible in the algebraically closed residue field. The conclusion is that there exists an extra level $K$ at $\ell$ on $E$ such that the pairs $(E',K')$ and $(E,K)$ are isomorphic in the sense of `FakeEllipticCurve.WithExtraLevel.Iso`, namely there is an isomorphism of the two fake elliptic curves as above which in addition matches the $T$-points factoring through $K'$ with those factoring through $K$.
--
--   This is the statement that extra level structures at $\ell$ are functorial in isomorphisms of fake elliptic curves, so that an extra level may be moved from one representative of a moduli point to any isomorphic curve. It is used in the study of the degeneracy maps and multiplicity counts on the quaternionic moduli tower, for instance in the finiteness of degeneracy morphisms and in the stabiliser-order computations for Galois frames.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_iso_of_iso.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_iso_of_iso
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] (ℓ : ℕ)
    (E E' : FakeEllipticCurve Λ N S) (h : FakeEllipticCurve.Iso E' E) (K' : E'.ExtraLevel ℓ) :
    ∃ K : E.ExtraLevel ℓ,
      FakeEllipticCurve.WithExtraLevel.Iso (⟨E', K'⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) ⟨E, K⟩ := by sorry
