-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_seq_forall_ne_not_iso_of_not_dvd_of_squarefree
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_seq_forall_ne_not_iso_of_not_dvd_of_squarefree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/8f1c4cfe-eee6-5f68-a071-4dec3a914290
-- title:
--   Infinitely many pairwise non-isomorphic fake elliptic curves over ℚ̄
-- statement:
--   Let $q$ and $q'$ be distinct primes and let $a,b\in\mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, that is: $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible precisely when $v$ contains $q$ or $q'$. Let $\Lambda\subset\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order, i.e. it contains $1$, is closed under multiplication, spans the algebra over $\mathbb{Q}$, is finitely generated, and is maximal among such submodules under inclusion. Let $N$ be a nonzero natural number which is squarefree and divisible by neither $q$ nor $q'$. Then there is a sequence $(E_n)_{n\in\mathbb{N}}$ of objects of type `FakeEllipticCurve Λ N (AlgebraicClosure ℚ)` — each consisting of a scheme $A$ with a structure morphism $f$ to $\operatorname{Spec}$ of the algebraic closure of $\mathbb{Q}$, a commutative relative group law on the functor of points of $f$, the property bundle asserting that $f$ is smooth, proper, with connected fibres and admitting a group law, fibres of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms of $A$ over the base which is multiplicative, additive on points, unital, normalised by a trace condition on the induced action on tangent spaces, and a level-$N$ structure morphism $\mathrm{lev}$ — such that for all $m\ne n$ the relation `FakeEllipticCurve.Iso (E m) (E n)` fails, i.e. there is no isomorphism of schemes over the base compatible with the group laws, commuting with the $\Lambda$-actions, and matching the points that factor through the respective level structures.
--
--   This is the statement that the set of isomorphism classes of fake elliptic curves (abelian surfaces with quaternionic multiplication by $\Lambda$ and level-$N$ structure) over an algebraic closure of $\mathbb{Q}$ is infinite, the geometric counterpart of the positive-dimensionality of the Shimura curve attached to $\Lambda$ and level $N$. It is used in the construction of a fake elliptic curve whose only automorphisms are $\pm 1$, i.e. in the selection of a rigid member of the moduli problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_seq_forall_ne_not_iso_of_not_dvd_of_squarefree.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_seq_forall_ne_not_iso_of_not_dvd_of_squarefree
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hNsq : Squarefree N) :
    ∃ E : ℕ → FakeEllipticCurve Λ N (AlgebraicClosure ℚ), ∀ m n : ℕ, m ≠ n → ¬ FakeEllipticCurve.Iso (E m) (E n) := by sorry
