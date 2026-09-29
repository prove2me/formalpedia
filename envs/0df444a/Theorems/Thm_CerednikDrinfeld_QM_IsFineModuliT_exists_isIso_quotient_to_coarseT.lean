-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuliT_exists_isIso_quotient_to_coarseT
-- name    : CerednikDrinfeld.QM.IsFineModuliT.exists_isIso_quotient_to_coarseT
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/4ee86789-2dc0-56d2-a673-c5a5c292b5ab
-- title:
--   Quotient of the level-ℓ fine scheme is mathcal Y_ℓ
-- statement:
--   The data are: primes $r \neq \bar r$ and a squarefree $N$ divisible by neither; a characteristic-zero discrete valuation ring $\mathcal O$, complete for the $\pi$-adic topology at an irreducible $\pi$, with residue ring of cardinality $r$ and $r\mathcal O = \pi\mathcal O$; rationals $a,b$ with $0 < a$ or $0 < b$ such that the completion of $\mathbb H[\mathbb Q,a,b]$ at a finite place $v$ is a division algebra exactly when $r$ or $\bar r$ lies in $v$, and a maximal order $\Lambda$ there; an auxiliary level $n \ge 3$ coprime to $r$, $\bar r$ and $N$. Further: $M \to \operatorname{Spec}\mathcal O$ with a point rule `ptF` making it a fine moduli scheme for fake elliptic curves with $\Lambda$-action, level-$N$ and full level-$n$ structure (the rule is constant on isomorphism classes, compatible with pullbacks, and bijective on $S$-points), $f_M$ separated, every finite subset of $M$ lying in an affine open; a group $G$ with a homomorphism $\rho$ to $\operatorname{Aut} M$ and labels $\chi : G \to \Lambda$ realising the level twists, as recorded by `IsLevelTwistAction`; for every prime $\ell \notin \{r,\bar r\}$ a scheme $\mathcal Y_\ell \to \operatorname{Spec}\mathcal O$ with a point rule `ptT` that is a coarse moduli scheme for pairs consisting of such a curve and an extra level-$\ell$ structure (a finite flat $\Lambda$-stable subgroup scheme of rank $\ell^2$ killed by $\ell$, disjoint from the level-$N$ structure); and, for one fixed $\ell$, a fine moduli scheme $M_\ell \to \operatorname{Spec}\mathcal O$ with point rule `ptFℓ` for objects carrying both a full level-$n$ and an extra level-$\ell$ structure, forgetful morphisms $\pi_\ell : M_\ell \to M$ and $p_\ell : M_\ell \to \mathcal Y_\ell$ over $\mathcal O$ compatible with the three point rules, a lift $\rho_\ell$ of the $G$-action to $M_\ell$ over $\mathcal O$ commuting with $\pi_\ell$, leaving $p_\ell$ invariant and twisting `ptFℓ` along $\chi$, and finally a quotient presentation $\pi'_\ell : M_\ell \to X'_\ell$ of $M_\ell$ by $\rho_\ell(G)$: invariant, integral, affine, surjective on underlying points, injective on sections over every open with image exactly the $G$-invariant sections, every $G$-stable affine open of $M_\ell$ being the preimage of an affine open of $X'_\ell$, together with $\pi_{X'_\ell} : X'_\ell \to \operatorname{Spec}\mathcal O$ through which $f_{M_\ell}$ factors via $\pi'_\ell$. The conclusion is that there is a morphism $e : X'_\ell \to \mathcal Y_\ell$ which is an isomorphism and satisfies $g_\ell \circ e = \pi_{X'_\ell}$ and $e \circ \pi'_\ell = p_\ell$.
--
--   This identifies the quotient of the level-$\ell$ fine moduli scheme by the twisting action of $G$ with the coarse moduli scheme $\mathcal Y_\ell$ of pairs, compatibly with the forgetful morphism $p_\ell$ and with the structure morphisms over $\mathcal O$; it is the step that makes the Hecke tower away from $r$ and $\bar r$ available as a quotient presentation. It is used in the construction of the level-$\ell$ fine moduli scheme with its quotient presentation from a separated fine moduli scheme of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuliT_exists_isIso_quotient_to_coarseT.lean

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

theorem CerednikDrinfeld.QM.IsFineModuliT.exists_isIso_quotient_to_coarseT

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
    ∃ (eXℓ : Xℓ' ⟶ 𝒴 ℓ), IsIso eXℓ ∧ eXℓ ≫ g ℓ = πXℓ' ∧ πℓ' ≫ eXℓ = pℓ := by sorry
