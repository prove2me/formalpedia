-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_iso_of_iso_of_directed_colimit_of_isUnit
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_iso_of_iso_of_directed_colimit_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/3d76b598-220d-58da-9ccd-79dd47a0bf42
-- title:
--   Descent of full-level isomorphisms along a directed colimit
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $a>0$ or $b>0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the base change of the algebra to the $v$-adic completion is a division algebra exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order and is maximal among orders under inclusion, let $N \geq 1$ and let $m$ be a natural number with $3 \leq m$. Let $\iota$ be a nonempty directed preorder, $(S_i)_{i \in \iota}$ commutative rings with transition homomorphisms $t_{ij} : S_i \to S_j$ for $i \leq j$ satisfying $t_{ii} = \mathrm{id}$ and $t_{jk} \circ t_{ij} = t_{ik}$, and let $L$ be a commutative ring with homomorphisms $c_i : S_i \to L$ such that $c_j \circ t_{ij} = c_i$, such that every element of $L$ is of the form $c_i(y)$, and such that $c_i(y) = c_i(z)$ implies $t_{ij}(y) = t_{ij}(z)$ for some $j \geq i$; thus $L$ is the colimit of the system. Assume moreover that the image of $m$ in $L$ is a unit. The assertion is: for every index $i$, every pair $v,w$ of fake elliptic curves over $S_i$ with $\Lambda$-action, level-$N$ structure and full level-$m$ structure, every pair $v',w'$ of such objects over $L$, if $v'$ and $w'$ are base changes of $v$ and $w$ along $c_i$ in the sense of `FakeEllipticCurve.WithFullLevel.IsPullback` (a map of the underlying schemes making a pullback square over $\mathrm{Spec}$ of the ring map, compatible with the relative group laws, the $\Lambda$-actions, the level-$N$ subschemes and the distinguished $m$-torsion section), and if $v'$ and $w'$ are isomorphic (an isomorphism of schemes over $\mathrm{Spec}\,L$ respecting group law, $\Lambda$-action, level-$N$ structure and carrying the full level-$m$ section to the other), then there are $j \geq i$ and objects $v_j, w_j$ over $S_j$ that are base changes of $v$ and $w$ along $t_{ij}$ in the same sense, with $v_j$ and $w_j$ isomorphic over $S_j$.
--
--   This is the isomorphism-descent half of the standard limit formalism for finitely presented data (as in EGA IV$_3$, 8.8.2.5 and 8.10.5), specialised to fake elliptic curves with $\Lambda$-action, level-$N$ structure and full level-$m$ structure: an isomorphism over the colimit ring already exists at a finite stage, after replacing the index by a larger one. It feeds into the corresponding existence statement [`CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_of_directed_colimit_of_isUnit`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_of_directed_colimit_of_isUnit), which underlies the representability of the rigidified moduli problem used in the Čerednik–Drinfeld description of Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_iso_of_iso_of_directed_colimit_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_iso_of_iso_of_directed_colimit_of_isUnit
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N] (m : ℕ) (hm : 3 ≤ m)
    (ι : Type) [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (S : ι → Type) [∀ i, CommRing (S i)]
    (t : ∀ i j, i ≤ j → (S i →+* S j))
    (ht₁ : ∀ i (h : i ≤ i), t i i h = RingHom.id (S i))
    (ht₂ : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k), (t j k hjk).comp (t i j hij) = t i k (hij.trans hjk))
    (L : Type) [CommRing L] (c : ∀ i, S i →+* L)
    (hc : ∀ i j (h : i ≤ j), (c j).comp (t i j h) = c i)
    (hcsurj : ∀ x : L, ∃ (i : ι) (y : S i), c i y = x)
    (hcker : ∀ (i : ι) (y z : S i), c i y = c i z → ∃ (j : ι) (h : i ≤ j), t i j h y = t i j h z)
    (hmL : IsUnit ((m : ℕ) : L)) :
    ∀ (i : ι) (v w : FakeEllipticCurve.WithFullLevel Λ N m (S i)) (v' w' : FakeEllipticCurve.WithFullLevel Λ N m L),
        FakeEllipticCurve.WithFullLevel.IsPullback (c i) v v' → FakeEllipticCurve.WithFullLevel.IsPullback (c i) w w' →
        FakeEllipticCurve.WithFullLevel.Iso v' w' →
        ∃ (j : ι) (h : i ≤ j) (vj wj : FakeEllipticCurve.WithFullLevel Λ N m (S j)),
          FakeEllipticCurve.WithFullLevel.IsPullback (t i j h) v vj ∧ FakeEllipticCurve.WithFullLevel.IsPullback (t i j h) w wj ∧
          FakeEllipticCurve.WithFullLevel.Iso vj wj := by sorry
