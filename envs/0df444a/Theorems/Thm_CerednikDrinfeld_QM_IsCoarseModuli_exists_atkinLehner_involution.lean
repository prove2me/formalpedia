-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuli_exists_atkinLehner_involution
-- name    : CerednikDrinfeld.QM.IsCoarseModuli.exists_atkinLehner_involution
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/782d303d-6ed4-5dfa-b0b8-cdbb9d943f5b
-- title:
--   Atkin–Lehner quotients and the involution wᵣ on coarse moduli
-- statement:
--   Fix primes $q$ and $q'$ with $q' \neq q$, rationals $a,b$ such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds for the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ — that is, $0 < a$ or $0 < b$, and for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra exactly when $v$ lies above $q$ or $q'$ — a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ that is an order maximal among orders under inclusion, a nonzero level $N$ divisible by neither $q$ nor $q'$, and $r$ equal to $q$ or to $q'$. Four assertions are made, in conjunction. First, over every commutative ring $S$ each fake elliptic curve $E$ of level $N$ with $\Lambda$-action admits an $E'$ with `E.IsAtkinLehnerQuotient r E'`: there are morphisms $\varphi : E.A \to E'.A$ and $\psi : E'.A \to E.A$ over $\mathrm{Spec}\,S$, each compatible with the relative group laws and commuting with the $\Lambda$-actions, such that, whenever $r \in \Lambda$, the composite $\varphi$ followed by $\psi$ is the action of $r$ on $E$ and $\psi$ followed by $\varphi$ the action of $r$ on $E'$; a point $P$ of $E$ over a base $t$ is killed by $\varphi$ precisely when it is killed by every $m \in \Lambda$ with $m\,\overline{m} = rn$ for some $n \in \mathbb{Z}$; and $\varphi$ carries points factoring through the level structure $E.\mathrm{lev}$ to points factoring through $E'.\mathrm{lev}$. Secondly, this relation is invariant under isomorphism in the source: isomorphic $E$, $E_1$ have isomorphic Atkin–Lehner quotients. Thirdly, it is compatible with base change along a ring homomorphism $\varphi : S \to S'$: if $F$ is the pullback of $E$ and $E'$, $F'$ are Atkin–Lehner quotients at $r$ of $E$, $F$, then $F'$ is the pullback of $E'$. Fourthly, for every commutative ring $B_0$, every scheme $\mathcal{X}$ with structure morphism $f : \mathcal{X} \to \mathrm{Spec}\,B_0$ and every assignment $\mathrm{pt}$ sending a ring $S$, a morphism $s : \mathrm{Spec}\,S \to \mathrm{Spec}\,B_0$ and a fake elliptic curve over $S$ to a morphism $\mathrm{Spec}\,S \to \mathcal{X}$ whose composite with $f$ is $s$, if `IsCoarseModuli Λ N 𝒳 f pt` holds (isomorphism-invariance and pullback-compatibility of $\mathrm{pt}$, bijectivity on points over algebraically closed fields, and the universal property among such assignments), then there is a unique $w : \mathcal{X} \to \mathcal{X}$ with $w$ followed by $f$ equal to $f$ and $(\mathrm{pt}\,S\,s\,E')_1 = (\mathrm{pt}\,S\,s\,E)_1$ followed by $w$ for every Atkin–Lehner pair $E, E'$ at $r$ over every $S$; and, as a separate final clause, every $w$ over $B_0$ with that intertwining property satisfies $w \circ w = \mathrm{id}_{\mathcal{X}}$.
--
--   This is the construction of the Atkin–Lehner involution $w_r$ at a prime $r$ where the quaternion algebra ramifies, realised on a coarse moduli scheme of fake elliptic curves with level $N$ structure, together with the moduli-theoretic facts about quotients by the two-sided ideal above $r$ that produce it. It is used in the Čerednik–Drinfeld part of the development, in the existence results for descent intertwining bases attached to moduli tower witnesses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCoarseModuli_exists_atkinLehner_involution.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.IsCoarseModuli.exists_atkinLehner_involution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (r : ℕ) (hr : r = q ∨ r = q') :

    (∀ (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S), ∃ E' : FakeEllipticCurve Λ N S, E.IsAtkinLehnerQuotient r E') ∧
    (∀ (S : Type) [CommRing S] (E E₁ E' E₁' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.Iso E E₁ → E.IsAtkinLehnerQuotient r E' → E₁.IsAtkinLehnerQuotient r E₁' → FakeEllipticCurve.Iso E' E₁') ∧
    (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (E E' : FakeEllipticCurve Λ N S) (F F' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E F → E.IsAtkinLehnerQuotient r E' → F.IsAtkinLehnerQuotient r F' →
      FakeEllipticCurve.IsPullback φ E' F') ∧

    (∀ {B₀ : Type} [CommRing B₀] (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of B₀))
      (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀)),
        FakeEllipticCurve Λ N S → SchemeHomOver s f),
      IsCoarseModuli Λ N 𝒳 f pt →
      ∃! w : 𝒳 ⟶ 𝒳, w ≫ f = f ∧
        ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀)) (E E' : FakeEllipticCurve Λ N S),
          E.IsAtkinLehnerQuotient r E' → (pt S s E').1 = (pt S s E).1 ≫ w) ∧
    (∀ {B₀ : Type} [CommRing B₀] (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of B₀))
      (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀)),
        FakeEllipticCurve Λ N S → SchemeHomOver s f),
      IsCoarseModuli Λ N 𝒳 f pt → ∀ w : 𝒳 ⟶ 𝒳, w ≫ f = f →
        (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀)) (E E' : FakeEllipticCurve Λ N S),
          E.IsAtkinLehnerQuotient r E' → (pt S s E').1 = (pt S s E).1 ≫ w) →
        w ≫ w = 𝟙 𝒳) := by sorry
