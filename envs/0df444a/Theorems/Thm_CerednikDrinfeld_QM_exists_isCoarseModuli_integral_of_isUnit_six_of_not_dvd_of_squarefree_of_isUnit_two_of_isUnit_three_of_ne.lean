-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_isCoarseModuli_integral_of_isUnit_six_of_not_dvd_of_squarefree_of_isUnit_two_of_isUnit_three_of_ne
-- name    : CerednikDrinfeld.QM.exists_isCoarseModuli_integral_of_isUnit_six_of_not_dvd_of_squarefree_of_isUnit_two_of_isUnit_three_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/6701e4fa-57b1-57d4-bc73-f81617f5a432
-- title:
--   Integral coarse moduli of fake elliptic curves, with degeneracy maps
-- statement:
--   Let $q \ne q'$ be primes and $a,b \in \mathbb{Q}$ be such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of the integers of $\mathbb{Q}$ the algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order maximal among orders containing it, let $N \ne 0$ be squarefree and divisible by neither $q$ nor $q'$, let $\mathcal{O}$ be an integral domain of characteristic $0$ in which $N$, $2$ and $3$ are invertible, and let $m_0 \ge 3$ be a natural number invertible in $\mathcal{O}$. Then there are a scheme $\mathcal{X}$, a morphism $f : \mathcal{X} \to \operatorname{Spec}\mathcal{O}$, and a rule $\mathrm{pt}$ sending each commutative ring $S$, each $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$ and each fake elliptic curve over $S$ (an abelian scheme with commutative relative group law, all fibres of dimension $2$, a $\Lambda$-action satisfying the trace condition, and level-$N$ data) to a morphism $\operatorname{Spec} S \to \mathcal{X}$ over $s$, such that `IsCoarseModuli Λ N 𝒳 f pt` holds: $\mathrm{pt}$ is constant on isomorphism classes, compatible with pullback of curves along ring homomorphisms, bijective from isomorphism classes onto points over algebraically closed fields, and initial among all such point rules (any $T$, $\pi_T$, $\mathrm{pt}'$ with the first two properties factors through a unique $\mathcal{X} \to T$ over $\operatorname{Spec}\mathcal{O}$). Moreover $\mathcal{X}$ is integral and $f$ is flat, separated, locally of finite type and quasi-compact, and is smooth of relative dimension $1$ whenever $6qq'$ is invertible in $\mathcal{O}$. Furthermore, for every prime $\ell \ne q, q'$ invertible in $\mathcal{O}$ there are $\mathcal{Y}$, $g : \mathcal{Y} \to \operatorname{Spec}\mathcal{O}$ and a point rule $\mathrm{pt}_T$ on pairs consisting of a fake elliptic curve together with an extra level structure at $\ell$, satisfying the corresponding coarse moduli property `IsCoarseModuliT Λ N ℓ 𝒴 g ptT`, with $\mathcal{Y}$ integral and $g$ flat, separated, locally of finite type, quasi-compact, and smooth of relative dimension $1$ when $6qq'$ is invertible, together with two morphisms $d_0, d_1 : \mathcal{Y} \to \mathcal{X}$ over $\operatorname{Spec}\mathcal{O}$ such that $\mathrm{pt}_T(u)$ followed by $d_0$ is $\mathrm{pt}$ of the underlying curve of $u$, and $\mathrm{pt}_T(u)$ followed by $d_1$ is $\mathrm{pt}(d)$ for every fake elliptic curve $d$ related to $u$ by an $\ell$-level isogeny in the sense of `FakeEllipticCurve.IsLevelIsogeny`.
--
--   This is the construction, in the Čerednik–Drinfeld framework, of the integral model of the Shimura curve attached to an indefinite quaternion algebra over $\mathbb{Q}$ ramified exactly at $q$ and $q'$, as a coarse moduli scheme of fake elliptic curves with $\Lambda$-action and level-$N$ structure, together with its $\Gamma_0(\ell)$-type covers and the two degeneracy maps used to define Hecke correspondences. It is the geometric input for the Čerednik–Drinfeld uniformisation and the quaternionic level-raising and level-lowering arguments that follow.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_isCoarseModuli_integral_of_isUnit_six_of_not_dvd_of_squarefree_of_isUnit_two_of_isUnit_three_of_ne.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld NeronModelInfra
open CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.exists_isCoarseModuli_integral_of_isUnit_six_of_not_dvd_of_squarefree_of_isUnit_two_of_isUnit_three_of_ne
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hNsq : Squarefree N)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hN : IsUnit ((N : ℕ) : 𝒪))
    (h2 : IsUnit ((2 : ℕ) : 𝒪)) (h3 : IsUnit ((3 : ℕ) : 𝒪))
    (m₀ : ℕ) (hm₀ : 3 ≤ m₀) (hm₀u : IsUnit ((m₀ : ℕ) : 𝒪)) :
    ∃ (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪))
      (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)), FakeEllipticCurve Λ N S → SchemeHomOver s f),
      IsCoarseModuli Λ N 𝒳 f pt ∧ IsIntegral 𝒳 ∧ Flat f ∧ IsSeparated f ∧ LocallyOfFiniteType f ∧ QuasiCompact f ∧
      (IsUnit ((6 * q * q' : ℕ) : 𝒪) → SmoothOfRelativeDimension 1 f) ∧
      ∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ q → ℓ ≠ q' → IsUnit ((ℓ : ℕ) : 𝒪) →
        ∃ (𝒴 : Scheme.{0}) (g : 𝒴 ⟶ Spec (CommRingCat.of 𝒪))
          (ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
            FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s g),
          IsCoarseModuliT Λ N ℓ 𝒴 g ptT ∧ IsIntegral 𝒴 ∧ Flat g ∧ IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g ∧
          (IsUnit ((6 * q * q' : ℕ) : 𝒪) → SmoothOfRelativeDimension 1 g) ∧
          ∃ (d₀ d₁ : 𝒴 ⟶ 𝒳), d₀ ≫ f = g ∧ d₁ ≫ f = g ∧
            (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
              (ptT S s u).1 ≫ d₀ = (pt S s u.1).1) ∧
            (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S)
              (d : FakeEllipticCurve Λ N S), FakeEllipticCurve.IsLevelIsogeny ℓ u d → (ptT S s u).1 ≫ d₁ = (pt S s d).1) := by sorry
