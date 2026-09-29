-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_of_directed_colimit_of_isUnit
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_of_directed_colimit_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/c9904a3e-9137-59d5-b25f-5c798c6bf018
-- title:
--   Fake elliptic curves with full level descend along directed colimits
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is a maximal order (an order maximal among orders), let $N \geq 1$ and $m \geq 3$. Let $\iota$ be a nonempty directed preorder, $(S_i)_{i}$ commutative rings with transition ring maps $t_{ij} : S_i \to S_j$ for $i \le j$ satisfying $t_{ii} = \mathrm{id}$ and $t_{jk} \circ t_{ij} = t_{ik}$, and let $L$ be a commutative ring with ring maps $c_i : S_i \to L$ satisfying $c_j \circ t_{ij} = c_i$, such that every element of $L$ is $c_i(y)$ for some $i$ and $y$, and $c_i(y) = c_i(z)$ implies $t_{ij}(y) = t_{ij}(z)$ for some $j \ge i$; thus $L$ is the colimit of the system. Assume $m$ is invertible in $L$. The conclusion is the conjunction of two statements about the groupoid of pairs $u = (E, \text{full level-}m\text{ structure})$ consisting of a fake elliptic curve over the base ring with $\Lambda$-action and level-$N$ datum together with a full level-$m$ structure. (A) Every such $u$ over $L$ is a base change: there are $i$ and $u_i$ over $S_i$ with `FakeEllipticCurve.WithFullLevel.IsPullback (c i) ui u`, i.e. a morphism $g$ from the total space of $u$ to that of $u_i$ forming a pullback square of the structure morphisms over $\mathrm{Spec}(c_i)$, compatible with the relative group laws, intertwining the $\Lambda$-actions, carrying points factoring through the level-$N$ subscheme to points factoring through that of $u_i$, and matching the distinguished sections. (B) For any $i$, any $v, w$ over $S_i$ and $v', w'$ over $L$ that are base changes of $v$ and $w$ along $c_i$ in this sense, an isomorphism $v' \cong w'$ (an isomorphism of total spaces over $\mathrm{Spec}\,L$ respecting group law, $\Lambda$-action, level-$N$ condition and the section) forces the existence of $j \ge i$ and base changes $v_j, w_j$ of $v, w$ along $t_{ij}$ with $v_j \cong w_j$.
--
--   These are the two colimit conditions that make the moduli problem of fake elliptic curves with $\Lambda$-action, level-$N$ datum and full level-$m$ structure locally of finite presentation in the sense of EGA IV$_3$ §8: objects over a filtered colimit come from a finite stage, and isomorphisms over the colimit are already present at some later stage. It is used in the construction of the extra-level variant of the statement and in the proof that the fine moduli problem is locally of finite presentation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_of_directed_colimit_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_of_directed_colimit_of_isUnit
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
    (∀ u : FakeEllipticCurve.WithFullLevel Λ N m L,
        ∃ (i : ι) (ui : FakeEllipticCurve.WithFullLevel Λ N m (S i)), FakeEllipticCurve.WithFullLevel.IsPullback (c i) ui u) ∧
    (∀ (i : ι) (v w : FakeEllipticCurve.WithFullLevel Λ N m (S i)) (v' w' : FakeEllipticCurve.WithFullLevel Λ N m L),
        FakeEllipticCurve.WithFullLevel.IsPullback (c i) v v' → FakeEllipticCurve.WithFullLevel.IsPullback (c i) w w' →
        FakeEllipticCurve.WithFullLevel.Iso v' w' →
        ∃ (j : ι) (h : i ≤ j) (vj wj : FakeEllipticCurve.WithFullLevel Λ N m (S j)),
          FakeEllipticCurve.WithFullLevel.IsPullback (t i j h) v vj ∧ FakeEllipticCurve.WithFullLevel.IsPullback (t i j h) w wj ∧
          FakeEllipticCurve.WithFullLevel.Iso vj wj) := by sorry
