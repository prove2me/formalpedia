-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_hom_eq_id_or_mapPt_eq_inv_of_not_dvd_of_squarefree
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_hom_eq_id_or_mapPt_eq_inv_of_not_dvd_of_squarefree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/7cbe97ea-6b61-5cf6-91f8-6ceda97b42f8
-- title:
--   Existence of a rigid fake elliptic curve over ℚ̄
-- statement:
--   Let $q\neq q'$ be primes, let $a,b\in\mathbb Q$ and suppose the quaternion algebra $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, that is, $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ every nonzero element of $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a unit exactly when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule which is a maximal order, i.e. $\Lambda$ contains $1$, is closed under multiplication, is finitely generated, spans the algebra over $\mathbb Q$, and is maximal among such submodules; let $N$ be a nonzero natural number, squarefree and divisible by neither $q$ nor $q'$. Then there is a fake elliptic curve $E$ in the sense of `FakeEllipticCurve Λ N (AlgebraicClosure ℚ)` — a scheme $A$ with a structure morphism $f$ to $\mathrm{Spec}$ of $\overline{\mathbb Q}$ carrying a commutative relative group law $L$ on its functor of points, smooth and proper with connected fibres of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms over the base which is additive, multiplicative, compatible with $L$ and satisfies the prescribed trace identity, together with the remaining data of the structure (a scheme $C$ and a level datum) — which is rigid in the following sense: for every isomorphism $e:A\xrightarrow{\ \sim\ }A$ with $f\circ e=f$ such that composing $T$-points with $e$ is a homomorphism for $L$ and such that $e$ commutes with the action of every element of $\Lambda$, either $e$ is the identity of $A$, or for every scheme $T$, every morphism $t$ from $T$ to the base and every $T$-point $P$ of $A$ over $t$, composing $P$ with $e$ gives the $L$-inverse of $P$.
--
--   This is the rigidity (no extra automorphisms beyond $\pm 1$) of a suitably generic point of the Shimura curve attached to $\Lambda$ and level $N$, stated for fake elliptic curves over an algebraic closure of $\mathbb Q$. It is used in the construction of the moduli tower witness, where a rigid object is needed to compute cardinalities of stabilisers in the Galois frame.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_forall_hom_eq_id_or_mapPt_eq_inv_of_not_dvd_of_squarefree.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_forall_hom_eq_id_or_mapPt_eq_inv_of_not_dvd_of_squarefree
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hNsq : Squarefree N) :
    ∃ E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ),
      ∀ (e : E.A ≅ E.A) (he : e.hom ≫ E.f = E.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
            mapPt e.hom he (E.L.mul t P Q) = E.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) →
        (∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E.act x) →
        e.hom = 𝟙 E.A ∨
          ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
            mapPt e.hom he P = E.L.inv t P := by sorry
