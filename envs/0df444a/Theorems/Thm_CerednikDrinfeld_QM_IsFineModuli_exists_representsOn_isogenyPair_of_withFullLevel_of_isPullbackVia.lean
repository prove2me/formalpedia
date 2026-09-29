-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_representsOn_isogenyPair_of_withFullLevel_of_isPullbackVia
-- name    : CerednikDrinfeld.QM.IsFineModuli.exists_representsOn_isogenyPair_of_withFullLevel_of_isPullbackVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/5b66d47e-7570-59aa-9749-ec28da4504f9
-- title:
--   Representability of level-preserving rᵈ-isogeny pairs over arbitrary bases
-- statement:
--   Fix a prime $r$, a nonzero $N$ with $r \nmid N$, and a prime $\bar r \neq r$. Let $\mathcal O$ be a commutative ring containing an element $\pi$ with $(r) = (\pi)$, in which $2$ is invertible, and let $O_{nr}$ be an $\mathcal O$-algebra. Let $a, b \in \mathbb Q$ be such that $\mathbb H[\mathbb Q, a, b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b r rbar`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the completed algebra $\mathbb H[\mathbb Q,a,b] \otimes_{\mathbb Q} \mathbb Q_v$ is a division algebra exactly when $v$ contains $r$ or $\bar r$. Let $\Lambda \subseteq \mathbb H[\mathbb Q,a,b]$ be a maximal order (an order not properly contained in another order) containing all rational integers, equipped with $\mu_\Lambda \in \Lambda$ satisfying $\mu_\Lambda^2 = -(r\bar r)$ and a map $*_\Lambda : \Lambda \to \Lambda$ with $\mu_\Lambda \, x^{*_\Lambda} = \bar x \, \mu_\Lambda$ for all $x$, and with a coordinate map $\mathrm{coord} : \Lambda \to W(\mathbb F_{r^2})^2$ satisfying `IsOrderCoord` (additive, sending $1$ to $(1,0)$, multiplicative for the Frobenius-twisted product rule on $W(\mathbb F_{r^2})^2$, injective, with dense image modulo all powers of $r$, and computing reduced traces). Let $A_0$ be a fake elliptic curve with $\Lambda$-action and level-$N$ structure over $O_{nr}/(\pi)$. Let $n \ge 3$ with $r \nmid n$, and let $M \to \operatorname{Spec}\mathcal O$ together with a point assignment $\mathrm{ptF}$ be a fine moduli scheme for fake elliptic curves with full level-$n$ structure in the sense of `IsFineModuli` (isomorphism-invariance, compatibility with base change, surjectivity and injectivity up to isomorphism). Let $C$ be a Noetherian $\mathcal O$-algebra in which $\pi$ is nilpotent, let $\psi : O_{nr} \to C$ be an $\mathcal O$-algebra map, and let $\mathfrak A$ be a fake elliptic curve over $C/(\pi)$ together with $g_{\mathfrak A} : \mathfrak A.A \to A_0.A$ exhibiting $\mathfrak A$ as the pullback of $A_0$ along the induced map $O_{nr}/(\pi) \to C/(\pi)$, in the sense of `FakeEllipticCurve.IsPullbackVia` (cartesian square, compatibility with the relative group laws and with the $\Lambda$-actions, and factorisation of level points). Then for every $d$, every ring $S$ that is simultaneously a $C/(\pi)$-algebra and an $\mathcal O$-algebra compatibly, every pair $u$ consisting of a fake elliptic curve over $S$ with a full level-$n$ structure, and every fake elliptic curve $A$ over $S$ with $g_A : A.A \to \mathfrak A.A$ exhibiting $A$ as the pullback of $\mathfrak A$ along $C/(\pi) \to S$ in the same sense, there exist a scheme $X$, a morphism $\xi : X \to \operatorname{Spec} S$ locally of finite presentation, and a family $\mathrm{pt}$ attaching to each $S$-algebra $T$, each pair of base changes of $u.1$ and $A$ to $T$, and each level-preserving isogeny pair $(\varphi, \varphi')$ of degree $r^d$ between them, a $T$-point of $X$ over $S$, such that `IsogenyPair.RepresentsOn` holds for $\mathrm{pt}$: it is invariant under isomorphisms of the data compatible with the base-change maps and the isogenies, natural in $T$, and every $T$-point of $X$ over $S$ arises from such an isogeny pair.
--
--   This is the local chart supplier for the Čerednik–Drinfeld uniformisation: it produces, over an arbitrary base $S$ over $C/(\pi)$, a scheme locally of finite presentation representing level-preserving $r^d$-isogeny pairs from a levelled fake elliptic curve to the constant curve pulled back from $A_0$. It is used in the construction of the functor representing rigidified fake elliptic curves stratified by isogeny type over unramified bases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_exists_representsOn_isogenyPair_of_withFullLevel_of_isPullbackVia.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts
import Definitions.Def_CerednikDrinfeld_QMIsogenyPairRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.IsFineModuli.exists_representsOn_isogenyPair_of_withFullLevel_of_isPullbackVia
    {r N : ℕ} [Fact r.Prime] [NeZero N] (hrN : ¬ r ∣ N) {rbar : ℕ} [Fact rbar.Prime] (hrr : rbar ≠ r)

    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π}) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} (hBq : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)

    (μΛ : ↥Λ) (hμΛ : (μΛ : ℍ[ℚ, a, b]) * (μΛ : ℍ[ℚ, a, b]) = -(((r * rbar : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (starΛ : ↥Λ → ↥Λ) (hstarΛ : ∀ x : ↥Λ, (μΛ : ℍ[ℚ, a, b]) * (starΛ x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μΛ)
    (h2 : IsUnit ((2 : ℕ) : 𝒪))

    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (ψ : Onr →ₐ[𝒪] C)

    (𝔄 : FakeEllipticCurve Λ N (C ⧸ Ideal.span {algebraMap 𝒪 C π})) (g𝔄 : 𝔄.A ⟶ A₀.A)
    (h𝔄 : FakeEllipticCurve.IsPullbackVia (FakeEllipticCurve.Rigidification.residueLeg π ψ) A₀ 𝔄 g𝔄) :
    ∀ (d : ℕ) (S : Type) [CommRing S] [Algebra (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S] [Algebra 𝒪 S] [IsScalarTower 𝒪 (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S]
      (u : FakeEllipticCurve.WithFullLevel Λ N n S)
      (A : FakeEllipticCurve Λ N S) (gA : A.A ⟶ 𝔄.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap (C ⧸ Ideal.span {algebraMap 𝒪 C π}) S) 𝔄 A gA),
      ∃ (X : Scheme.{0}) (ξ : X ⟶ Spec (CommRingCat.of S)) (_ : LocallyOfFinitePresentation ξ)
        (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d u.1 A ξ),
        FakeEllipticCurve.IsogenyPair.RepresentsOn r d u.1 A ξ pt := by sorry
