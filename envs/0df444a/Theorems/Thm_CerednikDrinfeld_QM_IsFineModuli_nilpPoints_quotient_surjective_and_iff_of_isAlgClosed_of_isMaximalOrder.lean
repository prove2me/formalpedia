-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_nilpPoints_quotient_surjective_and_iff_of_isAlgClosed_of_isMaximalOrder
-- name    : CerednikDrinfeld.QM.IsFineModuli.nilpPoints_quotient_surjective_and_iff_of_isAlgClosed_of_isMaximalOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/60d89189-7d48-5dc7-96db-2b2673d3344d
-- title:
--   Geometric points of the fine-to-coarse map: surjectivity and G-orbits
-- statement:
--   Fix primes $q \ne q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: $a>0$ or $b>0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, let $N \ne 0$ and $n$ be naturals, let $\mathcal{O}$ be a commutative ring with a distinguished element $\pi$, and let $M \to \operatorname{Spec}\mathcal{O}$, together with its assignment $\mathrm{ptF}$ of points to pairs (fake elliptic curve of level $N$, full level-$n$ structure), be a fine moduli scheme in the sense of `IsFineModuli` (iso-invariance, compatibility with base change, and bijectivity of $\mathrm{ptF}$ on $S$-points over $\operatorname{Spec}\mathcal{O}$ up to isomorphism of pairs), with $n$ a unit in $\mathcal{O}$. Let $G$ be a finite group acting by $\rho : G \to \operatorname{Aut} M$ with labels $\chi : G \to \Lambda$ satisfying `IsLevelTwistAction`: each $\rho(g)$ is a morphism over $\operatorname{Spec}\mathcal{O}$, a twist of a pair by $\chi(g)$ is realised on points by composing with $\rho(g)$, and $\chi$ is multiplicative, injective and surjective onto the units of $\Lambda$ modulo $n$. Let $\mathcal{X} \to \operatorname{Spec}\mathcal{O}$ with its point assignment $\mathrm{pt}$ be a coarse moduli scheme of level $N$ in the sense of `IsCoarseModuli` (iso-invariance, base-change compatibility, bijectivity up to isomorphism on geometric points over algebraically closed fields, and the universal property among such assignments), and let $p : M \to \mathcal{X}$ be a morphism over $\operatorname{Spec}\mathcal{O}$ which is invariant under all $\rho(h)$ and satisfies $\mathrm{ptF}(E,P)$ followed by $p$ equals $\mathrm{pt}(E)$ for all $S$, all $s$ and all pairs. Then for every algebraically closed field $k$ that is an $\mathcal{O}$-algebra in which $n$ is a unit, the map on $k$-points over the structure morphism induced by $p$, sending $\varphi : \operatorname{Spec} k \to M$ to $\varphi$ followed by $p$, is surjective onto the $k$-points of $\mathcal{X}$ over $\operatorname{Spec}\mathcal{O}$, and two such points $y,y'$ of $M$ have the same image if and only if $y' = y$ followed by $\rho(h)$ for some $h \in G$.
--
--   This identifies the geometric fibres of the projection from the fine moduli scheme with full level-$n$ structure to the coarse moduli scheme of fake elliptic curves as the orbits of the level-twisting group, the moduli-theoretic input for treating the coarse Shimura curve as a quotient of the fine one on points. It is used in the derivation of the Čerednik–Drinfeld uniformisation of the coarse moduli scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_nilpPoints_quotient_surjective_and_iff_of_isAlgClosed_of_isMaximalOrder.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega NeronModelInfra

theorem CerednikDrinfeld.QM.IsFineModuli.nilpPoints_quotient_surjective_and_iff_of_isAlgClosed_of_isMaximalOrder
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N n : ℕ) [NeZero N]
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF) (hn𝒪 : IsUnit ((n : ℕ) : 𝒪))
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut M) (χ : G → ↥Λ) (hρ : IsLevelTwistAction Λ N n M fM ptF G ρ χ)
    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)), FakeEllipticCurve Λ N S → SchemeHomOver s f)
    (h𝒳 : IsCoarseModuli Λ N 𝒳 f pt)
    (p : M ⟶ 𝒳) (hp : p ≫ f = fM) (hρp : ∀ h : G, (ρ h).hom ≫ p = p)
    (hp_pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N n S),
      (ptF S s u).1 ≫ p = (pt S s u.1).1)
    (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hnk : IsUnit ((n : ℕ) : k)) :
    Function.Surjective ((Scheme.nilpPoints.mapHom fM f p hp).app k) ∧
    ∀ y y' : (Scheme.nilpPoints fM).obj k,
      (Scheme.nilpPoints.mapHom fM f p hp).app k y = (Scheme.nilpPoints.mapHom fM f p hp).app k y' ↔
        ∃ h : G, y' = (Scheme.nilpPoints.mapHom fM fM (ρ h).hom (hρ.over_base h)).app k y := by sorry
