-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_finset_forall_not_iso_forall_quasiInverse_exists_eq_nsmulPt
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_finset_forall_not_iso_forall_quasiInverse_exists_eq_nsmulPt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/71713a0c-ef41-5830-bf15-aa11ace98d32
-- title:
--   Rigidity of Λ-linear quasi-inverses of [n] off finitely many classes
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$, and let $a,b\in\mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: either $a>0$ or $b>0$, and for every height-one prime $v$ of the integers of $\mathbb{Q}$ the base change of $\mathbb{H}[\mathbb{Q},a,b]$ to the $v$-adic completion has all its nonzero elements invertible precisely when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ that is a maximal order (it contains $1$, is closed under multiplication, spans the algebra over $\mathbb{Q}$, is finitely generated, and is maximal among such submodules), let $N$ be a nonzero natural number and let $n>0$. Then there are a natural number $m$ and a family $S_0,\dots,S_{m-1}$ of fake elliptic curves for $\Lambda$ of level $N$ over $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ with the following property. Let $E$ be such a fake elliptic curve which is not isomorphic, in the sense of `FakeEllipticCurve.Iso` (an isomorphism of its total space over the base compatible with the relative group laws on $T$-points, with the $\Lambda$-actions, and with factorisation through the level morphism `lev`), to any $S_j$. Let $\varphi,\psi : E.A \to E.A$ be morphisms over $\mathrm{Spec}$ of the base ($\varphi \circ$ and $\psi\circ$ followed by $E.f$ equals $E.f$) such that each is additive on $T$-valued points for every base scheme $T$ and every $T$-point $t$ of the base (postcomposition commutes with `E.L.mul`), each commutes with the action of every $x\in\Lambda$, and on every $T$-valued point $P$ both composites, $\varphi$ followed by $\psi$ and $\psi$ followed by $\varphi$, equal the $n$-fold sum $\mathrm{nsmulPt}\ E.L\ t\ n\ P$. Then there is a natural number $k$ such that, on all $T$-valued points, postcomposition with $\varphi$ is either the $n$-fold-type multiplication $\mathrm{nsmulPt}\ E.L\ t\ k$ or its inverse for the group law $E.L$.
--
--   This is the rigidity statement that, outside a finite list of isomorphism classes, the commutant of the $\Lambda$-action on a fake elliptic curve over $\overline{\mathbb{Q}}$ contains no elements other than the integer multiplications, so that a $\Lambda$-linear endomorphism admitting a two-sided quasi-inverse with composite $[n]$ must be $\pm[k]$; the finitely many excluded classes are those with extra (imaginary quadratic) endomorphisms. It is used for the case $n=1$, giving that the only $\Lambda$-linear automorphisms are $\pm\mathrm{id}$, and for the level-$\ell$ case, giving injectivity properties of quotients by level isogenies.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_finset_forall_not_iso_forall_quasiInverse_exists_eq_nsmulPt.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_finset_forall_not_iso_forall_quasiInverse_exists_eq_nsmulPt
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N] (n : ℕ) (hn : 0 < n) :
    ∃ (m : ℕ) (S : Fin m → FakeEllipticCurve Λ N (AlgebraicClosure ℚ)),
      ∀ E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ), (∀ j : Fin m, ¬ FakeEllipticCurve.Iso E (S j)) →
        ∀ (φ : E.A ⟶ E.A) (hφ : φ ≫ E.f = E.f) (ψ : E.A ⟶ E.A) (hψ : ψ ≫ E.f = E.f),
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
              mapPt φ hφ (E.L.mul t P Q) = E.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
          (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E.act x) →
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
              mapPt ψ hψ (E.L.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) →
          (∀ x : ↥Λ, E.act x ≫ ψ = ψ ≫ E.act x) →
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
              mapPt ψ hψ (mapPt φ hφ P) = nsmulPt E.L t n P ∧ mapPt φ hφ (mapPt ψ hψ P) = nsmulPt E.L t n P) →
          ∃ k : ℕ,
            (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
                mapPt φ hφ P = nsmulPt E.L t k P) ∨
            (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
                mapPt φ hφ P = E.L.inv t (nsmulPt E.L t k P)) := by sorry
