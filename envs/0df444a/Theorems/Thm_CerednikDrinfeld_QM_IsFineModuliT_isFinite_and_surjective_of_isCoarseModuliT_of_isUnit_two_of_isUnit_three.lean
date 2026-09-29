-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuliT_isFinite_and_surjective_of_isCoarseModuliT_of_isUnit_two_of_isUnit_three
-- name    : CerednikDrinfeld.QM.IsFineModuliT.isFinite_and_surjective_of_isCoarseModuliT_of_isUnit_two_of_isUnit_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/b8feda26-c336-5752-b080-6847a0623473
-- title:
--   Finiteness and surjectivity of the level-forgetting map p_ℓ
-- statement:
--   Fix primes $r \neq \bar r$ and a nonzero $N$ with $r \nmid N$, $\bar r \nmid N$ and $N$ squarefree. Let $\mathcal O$ be a characteristic-zero domain which is a discrete valuation ring in which $2$ and $3$ are units, with an irreducible element $\pi$ such that $\mathcal O$ is $\pi$-adically complete, $\#(\mathcal O/\pi) = r$ and $(r) = (\pi)$. Let $a, b \in \mathbb Q$ be such that $\mathbb H[\mathbb Q, a, b]$ satisfies $0 < a$ or $0 < b$ and, for each height-one prime $v$ of $\mathcal O_{\mathbb Q}$, the $v$-adic completion is a division algebra exactly when $v$ contains $r$ or $\bar r$; let $\Lambda$ be a maximal order in it. Let $n \geq 3$ be prime to $r$, $\bar r$ and $N$. The data are: a scheme $M$ over $\operatorname{Spec} \mathcal O$ with a point rule $\mathrm{pt}_F$ on fake elliptic curves with level-$N$ and full level-$n$ structure making it a fine moduli scheme (the rule is constant on isomorphism classes, compatible with base change, and bijective on $S$-points for every $S$); a group $G$ with $\rho : G \to \operatorname{Aut} M$ and labels $\chi : G \to \Lambda$ forming a level-twist action (the automorphisms are over the base, twisting an object by $\chi(h)$ composes the point with $\rho(h)$, and $\chi$ is multiplicative, injective and surjective modulo $n$); for every prime $\ell \neq r, \bar r$ a scheme $\mathcal Y_\ell$ over $\operatorname{Spec}\mathcal O$ with a point rule $\mathrm{pt}_{T,\ell}$ on pairs consisting of a fake elliptic curve with level-$N$ structure and an extra level-$\ell$ structure (a $\Lambda$-stable finite flat closed subgroup scheme of rank $\ell^2$ killed by $\ell$, disjoint from the level structure, geometrically $(\mathbb Z/\ell)^2$), which is a coarse moduli scheme in the sense of `IsCoarseModuliT`; and, for one fixed such $\ell$, a scheme $M_\ell$ over $\operatorname{Spec}\mathcal O$ with a point rule $\mathrm{pt}_{F,\ell}$ on triples (object with full level $n$ together with an extra level-$\ell$ structure) which is a fine moduli scheme in the sense of `IsFineModuliT`, forgetful morphisms $\pi_\ell : M_\ell \to M$ and $p_\ell : M_\ell \to \mathcal Y_\ell$ over $\operatorname{Spec}\mathcal O$ compatible with the three point rules, and a lift $\rho_\ell : G \to \operatorname{Aut} M_\ell$ of the action which is over the base, intertwines $\pi_\ell$ with $\rho$, fixes $p_\ell$, and satisfies the twisting rule: whenever an isomorphism $e$ over the base exhibits $u'$ as a twist of $u$ by $\chi(h)$ in the sense of `FakeEllipticCurve.WithFullLevel.IsTwistVia` and matches the extra level subgroups $C$, $C'$ on points, then $\mathrm{pt}_{F,\ell}(u', C')$ equals $\mathrm{pt}_{F,\ell}(u, C)$ followed by $\rho_\ell(h)$. The conclusion is that $p_\ell$ is a finite morphism and its underlying map of topological spaces is surjective.
--
--   This expresses $\mathcal Y_\ell$ as the quotient of the fine moduli scheme of triples by the level-twisting action of $G$, in the form needed for the Čerednik–Drinfeld tower: forgetting the auxiliary full level $n$ from the moduli of triples onto the coarse moduli of pairs is a finite surjection. It is used in the construction of the tower of Shimura curves at level $N\ell$ away from $r$ and $\bar r$, in particular in deducing geometric properties of $\mathcal Y_\ell$ from those of $M_\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuliT_isFinite_and_surjective_of_isCoarseModuliT_of_isUnit_two_of_isUnit_three.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_HeckeTower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsFineModuliT.isFinite_and_surjective_of_isCoarseModuliT_of_isUnit_two_of_isUnit_three

    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N) (hN : Squarefree N)

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (h2 : IsUnit ((2 : ℕ) : 𝒪)) (h3 : IsUnit ((3 : ℕ) : 𝒪))
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (hrbarn : ¬ rbar ∣ n) (hnN : Nat.Coprime n N)
    (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (G : Type) [Group G] (ρ : G →* Aut M) (χ : G → ↥Λ) (hρ : IsLevelTwistAction Λ N n M fM ptF G ρ χ)

    (𝒴 : HeckeTower.AwayPrime r rbar → Scheme.{0}) (g : ∀ ℓ : HeckeTower.AwayPrime r rbar, 𝒴 ℓ ⟶ Spec (CommRingCat.of 𝒪))
    (ptT : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S → SchemeHomOver s (g ℓ))
    (h𝒴 : ∀ ℓ : HeckeTower.AwayPrime r rbar, IsCoarseModuliT Λ N (ℓ.1 : ℕ) (𝒴 ℓ) (g ℓ) (ptT ℓ))

    (ℓ : HeckeTower.AwayPrime r rbar)
    (Mℓ : Scheme.{0}) (fMℓ : Mℓ ⟶ Spec (CommRingCat.of 𝒪))
    (ptFℓ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N n S),
      u.1.ExtraLevel (ℓ.1 : ℕ) → SchemeHomOver s fMℓ)
    (hMℓ : IsFineModuliT Λ N n (ℓ.1 : ℕ) Mℓ fMℓ ptFℓ)
    (πℓ : Mℓ ⟶ M) (hπℓf : πℓ ≫ fM = fMℓ)
    (hπℓ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N n S)
      (C : u.1.ExtraLevel (ℓ.1 : ℕ)), (ptFℓ S s u C).1 ≫ πℓ = (ptF S s u).1)
    (pℓ : Mℓ ⟶ 𝒴 ℓ) (hpℓg : pℓ ≫ g ℓ = fMℓ)
    (hpℓ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N n S)
      (C : u.1.ExtraLevel (ℓ.1 : ℕ)), (ptFℓ S s u C).1 ≫ pℓ = (ptT ℓ S s ⟨u.1, C⟩).1)
    (ρℓ : G →* Aut Mℓ) (hρℓf : ∀ h : G, (ρℓ h).hom ≫ fMℓ = fMℓ)
    (hρℓπ : ∀ h : G, (ρℓ h).hom ≫ πℓ = πℓ ≫ (ρ h).hom) (hρℓp : ∀ h : G, (ρℓ h).hom ≫ pℓ = pℓ)
    (hρℓtw : ∀ (h : G) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u u' : FakeEllipticCurve.WithFullLevel Λ N n S) (C : u.1.ExtraLevel (ℓ.1 : ℕ)) (C' : u'.1.ExtraLevel (ℓ.1 : ℕ))
      (e : u.1.A ≅ u'.1.A) (he : e.hom ≫ u'.1.f = u.1.f),
      FakeEllipticCurve.WithFullLevel.IsTwistVia (χ h) u u' e he →
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
          FactorsThrough C.levK P ↔ FactorsThrough C'.levK (mapPt e.hom he P)) →
        (ptFℓ S s u' C').1 = (ptFℓ S s u C).1 ≫ (ρℓ h).hom)
    : IsFinite pℓ ∧ Function.Surjective pℓ.base := by sorry
