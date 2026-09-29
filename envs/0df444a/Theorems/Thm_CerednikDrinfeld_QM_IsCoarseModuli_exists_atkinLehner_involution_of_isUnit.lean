-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuli_exists_atkinLehner_involution_of_isUnit
-- name    : CerednikDrinfeld.QM.IsCoarseModuli.exists_atkinLehner_involution_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/ef04ceae-1ceb-519c-933b-9bfc958c22e9
-- title:
--   Atkin–Lehner involution at r on coarse moduli, r invertible
-- statement:
--   Fix distinct primes $q \neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_\mathbb{Q}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_\mathbb{Q} \mathbb{Q}_v$ is a division algebra exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order maximal among orders, let $N \neq 0$ with $q \nmid N$ and $q' \nmid N$, and let $r$ be $q$ or $q'$. Five assertions are made. (i) For every commutative ring $S$ in which the image of $r$ is a unit, every $E \in$ `FakeEllipticCurve Λ N S` admits an $E'$ with `E.IsAtkinLehnerQuotient r E'`, i.e. morphisms $\varphi : E.A \to E'.A$ and $\psi : E'.A \to E.A$ over $S$, each compatible with the relative group laws and commuting with the $\Lambda$-actions, with $\varphi \psi$ and $\psi \varphi$ equal to the action of $r$ whenever $r \in \Lambda$, with the kernel of $\varphi$ on $T$-points characterised as those $P$ killed by every $m \in \Lambda$ satisfying $m\bar{m} = rn$ for some $n \in \mathbb{Z}$, and with $\varphi$ carrying points factoring through the level structure of $E$ to points factoring through that of $E'$. (ii) Over such $S$, if $E \cong E_1$ and $E'$, $E_1'$ are Atkin–Lehner quotients at $r$ of $E$, $E_1$, then $E' \cong E_1'$. (iii) For a ring homomorphism $\phi : S \to S'$ with $r$ invertible in $S$, if $F$ is the pullback of $E$ along $\phi$ and $E'$, $F'$ are Atkin–Lehner quotients at $r$ of $E$, $F$, then $F'$ is the pullback of $E'$ along $\phi$. (iv) For every commutative ring $B_0$ with $r$ invertible, every scheme $\mathcal{X}$ with a morphism $f : \mathcal{X} \to \operatorname{Spec} B_0$ and every assignment `pt` sending a ring $S$, a morphism $s : \operatorname{Spec} S \to \operatorname{Spec} B_0$ and a fake elliptic curve over $S$ to a morphism $\operatorname{Spec} S \to \mathcal{X}$ over $s$, if `IsCoarseModuli Λ N 𝒳 f pt` holds then there is a unique $w : \mathcal{X} \to \mathcal{X}$ with $w$ followed by $f$ equal to $f$ and $\mathrm{pt}(S,s,E') = \mathrm{pt}(S,s,E)$ followed by $w$ whenever $E'$ is an Atkin–Lehner quotient at $r$ of $E$. (v) Under the same hypotheses, any $w$ over $\operatorname{Spec} B_0$ with that compatibility property satisfies $w \circ w = \mathrm{id}_\mathcal{X}$.
--
--   This is the construction of the Atkin–Lehner involution $w_r$ at a prime $r$ of ramification of the indefinite quaternion algebra, acting on a coarse moduli scheme of fake elliptic curves with $\Lambda$-action and level-$N$ structure, in the restricted setting of bases in which $r$ is invertible (no assertion is made in characteristic $r$). It is used by [`CerednikDrinfeld.QM.exists_W_of_coarse_of_two_mul_dvd`](thm.html#CerednikDrinfeld.QM.exists_W_of_coarse_of_two_mul_dvd) to produce the involutions on Shimura curves needed downstream.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCoarseModuli_exists_atkinLehner_involution_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.IsCoarseModuli.exists_atkinLehner_involution_of_isUnit
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (r : ℕ) (hr : r = q ∨ r = q') :

    (∀ (S : Type) [CommRing S], IsUnit ((r : ℕ) : S) → ∀ (E : FakeEllipticCurve Λ N S), ∃ E' : FakeEllipticCurve Λ N S, E.IsAtkinLehnerQuotient r E') ∧
    (∀ (S : Type) [CommRing S], IsUnit ((r : ℕ) : S) → ∀ (E E₁ E' E₁' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.Iso E E₁ → E.IsAtkinLehnerQuotient r E' → E₁.IsAtkinLehnerQuotient r E₁' → FakeEllipticCurve.Iso E' E₁') ∧
    (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S'), IsUnit ((r : ℕ) : S) →
      ∀ (E E' : FakeEllipticCurve Λ N S) (F F' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E F → E.IsAtkinLehnerQuotient r E' → F.IsAtkinLehnerQuotient r F' →
      FakeEllipticCurve.IsPullback φ E' F') ∧

    (∀ {B₀ : Type} [CommRing B₀], IsUnit ((r : ℕ) : B₀) → ∀ (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of B₀))
      (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀)),
        FakeEllipticCurve Λ N S → SchemeHomOver s f),
      IsCoarseModuli Λ N 𝒳 f pt →
      ∃! w : 𝒳 ⟶ 𝒳, w ≫ f = f ∧
        ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀)) (E E' : FakeEllipticCurve Λ N S),
          E.IsAtkinLehnerQuotient r E' → (pt S s E').1 = (pt S s E).1 ≫ w) ∧
    (∀ {B₀ : Type} [CommRing B₀], IsUnit ((r : ℕ) : B₀) → ∀ (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of B₀))
      (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀)),
        FakeEllipticCurve Λ N S → SchemeHomOver s f),
      IsCoarseModuli Λ N 𝒳 f pt → ∀ w : 𝒳 ⟶ 𝒳, w ≫ f = f →
        (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀)) (E E' : FakeEllipticCurve Λ N S),
          E.IsAtkinLehnerQuotient r E' → (pt S s E').1 = (pt S s E).1 ≫ w) →
        w ≫ w = 𝟙 𝒳) := by sorry
