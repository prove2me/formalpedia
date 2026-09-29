-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuliT_exists_isCoarseModuliT_of_quotient
-- name    : CerednikDrinfeld.QM.IsFineModuliT.exists_isCoarseModuliT_of_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/43468b42-5890-517c-87c7-b65472d74ace
-- title:
--   Quotient of the level-ℓ fine scheme is coarse moduli
-- statement:
--   Fix primes $r\neq\bar r$ and $N\geq 1$ squarefree with $r\nmid N$, $\bar r\nmid N$; let $\mathcal O$ be a characteristic-zero domain which is a discrete valuation ring, $\pi\in\mathcal O$ irreducible, $\mathcal O$ complete for the $\pi$-adic topology, with residue ring of cardinality $r$ and $(r)=(\pi)$. Let $a,b\in\mathbb Q$ satisfy $0<a$ or $0<b$ and be such that $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra exactly at the places $v$ above $r$ and $\bar r$, and let $\Lambda$ be a maximal order in it. Fix $n\geq 3$ with $r\nmid n$, $\bar r\nmid n$ and $\gcd(n,N)=1$. The data are: a scheme $M$ over $\operatorname{Spec}\mathcal O$ with a rule $\mathrm{ptF}$ assigning to each fake elliptic curve of level $N$ with full level-$n$ structure over a ring $S$ a point of $M$ over a given $s:\operatorname{Spec}S\to\operatorname{Spec}\mathcal O$, making $M$ a fine moduli scheme (the rule is invariant under isomorphism, compatible with pullback, and bijective on $S$-valued points for every $S$); separatedness of $M\to\operatorname{Spec}\mathcal O$ and the property that every finite set of points of $M$ lies in an affine open; a group $G$ with $\rho:G\to\operatorname{Aut}M$ and a labelling $\chi:G\to\Lambda$ constituting a level-twist action (the automorphisms are over the base, twisting the level-$n$ structure by $\chi(h)$ transports $\mathrm{ptF}$ by $\rho(h)$, and $\chi$ is multiplicative, injective and surjective modulo $n$); a family of coarse moduli schemes $\mathcal Y_\ell$ for pairs (curve, extra level-$\ell$ structure), indexed by primes $\ell\notin\{r,\bar r\}$, with rules $\mathrm{ptT}$; and, for one such $\ell$, a fine moduli scheme $M_\ell$ over $\operatorname{Spec}\mathcal O$ for triples (curve, full level $n$, extra level $\ell$) with rule $\mathrm{ptF}_\ell$, forgetful morphisms $\pi_\ell:M_\ell\to M$ and $p_\ell:M_\ell\to\mathcal Y_\ell$ over $\mathcal O$ compatible with the three rules, and a lift $\rho_\ell:G\to\operatorname{Aut}M_\ell$ which is over the base, intertwines $\pi_\ell$ with $\rho$, fixes $p_\ell$, and satisfies the twisting law: whenever $e$ is an isomorphism of the underlying curves over $S$ compatible with the structural morphisms which is a homomorphism for the group laws, $\Lambda$-equivariant, matches the level-$N$ structures, carries $\chi(h)$ applied to the level-$n$ point of $u$ to that of $u'$, and matches the extra level-$\ell$ subschemes of $C$ and $C'$, then $\mathrm{ptF}_\ell(u',C')$ equals $\mathrm{ptF}_\ell(u,C)$ followed by $\rho_\ell(h)$. Finally, let $\pi_\ell':M_\ell\to X_\ell'$ be $\rho_\ell$-invariant, integral, affine, surjective on points, with $\pi_\ell'{}^{\sharp}$ injective on every open and with image exactly the $\rho_\ell$-invariant sections, such that every $\rho_\ell$-invariant affine open of $M_\ell$ is the preimage of an affine open of $X_\ell'$, and let $\pi_{X_\ell'}:X_\ell'\to\operatorname{Spec}\mathcal O$ satisfy $\pi_\ell'$ followed by $\pi_{X_\ell'}$ equal to $M_\ell\to\operatorname{Spec}\mathcal O$. The conclusion is the existence of a rule $\mathrm{ptT}'$ assigning to every pair (fake elliptic curve of level $N$ over $S$, extra level-$\ell$ structure) a point of $X_\ell'$ over $s$, which makes $X_\ell'$ with $\pi_{X_\ell'}$ a coarse moduli scheme for such pairs — invariance under isomorphism of pairs, compatibility with pullback along ring homomorphisms, bijectivity up to isomorphism on points valued in algebraically closed fields, and the universal property that any rule of the same kind into a scheme $T$ over $\operatorname{Spec}\mathcal O$ factors through $X_\ell'$ by a unique morphism over the base — and which satisfies $\mathrm{ptT}'(E,C)=\mathrm{ptF}_\ell(u,C)$ followed by $\pi_\ell'$ for every full level-$n$ structure $u$ on $E$.
--
--   This is the descent of the moduli interpretation along a finite-group quotient, one level up in the Hecke tower: the quotient of the fine moduli scheme of triples (fake elliptic curve, full level-$n$ structure, extra level-$\ell$ structure) by the level-twisting action is identified as a coarse moduli scheme of pairs (curve, extra level-$\ell$ structure) over $\mathcal O$. It is used to compare such a quotient with the given coarse moduli scheme $\mathcal Y_\ell$ and to deduce finiteness and surjectivity properties of the comparison morphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuliT_exists_isCoarseModuliT_of_quotient.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_HeckeTower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsFineModuliT.exists_isCoarseModuliT_of_quotient

    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N) (hN : Squarefree N)

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (hrbarn : ¬ rbar ∣ n) (hnN : Nat.Coprime n N)
    (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (hsep : IsSeparated fM) (hfin : ∀ F : Finset M, ∃ U : M.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
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

    (Xℓ' : Scheme.{0}) (πℓ' : Mℓ ⟶ Xℓ') (hπℓ' : ∀ h : G, (ρℓ h).hom ≫ πℓ' = πℓ')
    (hintℓ' : IsIntegralHom πℓ') (haffℓ' : IsAffineHom πℓ') (hsurjℓ' : Function.Surjective πℓ'.base)
    (hsecℓ' : ∀ V : Xℓ'.Opens, Function.Injective (πℓ'.app V))
    (hinvℓ' : ∀ V : Xℓ'.Opens, Set.range (πℓ'.app V) =
          {s | ∀ h : G, (ρℓ h).hom.appLE (πℓ' ⁻¹ᵁ V) (πℓ' ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπℓ' h]) s = s})
    (hopenℓ' : ∀ U : Mℓ.Opens, IsAffineOpen U → (∀ h : G, (ρℓ h).hom ⁻¹ᵁ U = U) → ∃ V : Xℓ'.Opens, IsAffineOpen V ∧ πℓ' ⁻¹ᵁ V = U)
    (πXℓ' : Xℓ' ⟶ Spec (CommRingCat.of 𝒪)) (hπXℓ' : πℓ' ≫ πXℓ' = fMℓ) :
    ∃ ptT' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
        FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S → SchemeHomOver s πXℓ',
      IsCoarseModuliT Λ N (ℓ.1 : ℕ) Xℓ' πXℓ' ptT' ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (u : FakeEllipticCurve.WithFullLevel Λ N n S) (C : u.1.ExtraLevel (ℓ.1 : ℕ)),
        (ptT' S s ⟨u.1, C⟩).1 = (ptFℓ S s u C).1 ≫ πℓ' := by sorry
