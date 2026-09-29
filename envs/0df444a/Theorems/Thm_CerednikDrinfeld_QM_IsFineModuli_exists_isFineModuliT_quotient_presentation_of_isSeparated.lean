-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_isFineModuliT_quotient_presentation_of_isSeparated
-- name    : CerednikDrinfeld.QM.IsFineModuli.exists_isFineModuliT_quotient_presentation_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/005540ff-c7fb-5625-acde-badd40d88e22
-- title:
--   Level-ℓ fine moduli scheme and its quotient presentation
-- statement:
--   Fix primes $r \neq \bar r$ and a squarefree $N \neq 0$ divisible by neither, a characteristic-zero domain $\mathcal{O}$ that is a discrete valuation ring, an irreducible $\pi \in \mathcal{O}$ with $\mathcal{O}$ $(\pi)$-adically complete, residue cardinality $\#(\mathcal{O}/(\pi)) = r$ and $(r) = (\pi)$, rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b r rbar` (namely $0 < a$ or $0 < b$, and for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra exactly when $v$ contains $r$ or $\bar r$), a maximal order $\Lambda$, and an integer $n \geq 3$ prime to $r$, $\bar r$ and $N$. Let $f_M : M \to \operatorname{Spec}\mathcal{O}$ with a point rule $\mathrm{ptF}$ on fake elliptic curves with full level $n$ be a fine moduli datum (`IsFineModuli`: isomorphism-invariance, pullback-compatibility, and bijectivity on objects over every ring), with $f_M$ separated, every finite subset of $M$ contained in an affine open, and $\rho : G \to \operatorname{Aut} M$, $\chi : G \to \Lambda$ a level-twist action. Let $g_\ell : \mathcal{Y}_\ell \to \operatorname{Spec}\mathcal{O}$, for $\ell$ a prime distinct from $r,\bar r$, be coarse moduli for pairs (fake elliptic curve, extra level $\ell$). Then for each such $\ell$ there exist $f_{M_\ell} : M_\ell \to \operatorname{Spec}\mathcal{O}$ and a point rule on triples (full level $n$, extra level $\ell$) satisfying `IsFineModuliT`, forgetful maps $\pi_\ell : M_\ell \to M$ and $p_\ell : M_\ell \to \mathcal{Y}_\ell$ over $\mathcal{O}$ compatible with the point rules, a lift $\rho_\ell : G \to \operatorname{Aut} M_\ell$ over the base which commutes with $\pi_\ell$ via $\rho$, fixes $p_\ell$, and twists the full level according to $\chi$, with $f_{M_\ell}$ locally of finite type, together with $\pi_\ell' : M_\ell \to X_\ell'$ realising $X_\ell'$ as the quotient by $\rho_\ell(G)$ (invariant, integral, affine, surjective on points, injective on sections with image the $\rho_\ell(G)$-invariants, every $\rho_\ell(G)$-stable affine open of $M_\ell$ a preimage of an affine open), a structure morphism $\pi_{X_\ell'}$ with $\pi_\ell'$ followed by $\pi_{X_\ell'}$ equal to $f_{M_\ell}$, and an isomorphism $e_{X_\ell} : X_\ell' \to \mathcal{Y}_\ell$ over $\mathcal{O}$, such that $\pi_\ell'$ followed by $e_{X_\ell}$ equals $p_\ell$.
--
--   This packages the construction of the integral model carrying both a rigidifying full level $n$ and a $\Gamma_0(\ell)$-type extra level on fake elliptic curves, and identifies the coarse space $\mathcal{Y}_\ell$ with the quotient of the fine model by the level-twisting group action. It is used in the Čerednik–Drinfeld uniformisation statement for Shimura curves with Atkin–Lehner data at fine level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_exists_isFineModuliT_quotient_presentation_of_isSeparated.lean

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

theorem CerednikDrinfeld.QM.IsFineModuli.exists_isFineModuliT_quotient_presentation_of_isSeparated

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
    :
    ∀ (ℓ : HeckeTower.AwayPrime r rbar),
      ∃

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

        (hfMℓ : LocallyOfFiniteType fMℓ)

        (Xℓ' : Scheme.{0}) (πℓ' : Mℓ ⟶ Xℓ') (hπℓ' : ∀ h : G, (ρℓ h).hom ≫ πℓ' = πℓ')
        (hintℓ' : IsIntegralHom πℓ') (haffℓ' : IsAffineHom πℓ') (hsurjℓ' : Function.Surjective πℓ'.base)
        (hsecℓ' : ∀ V : Xℓ'.Opens, Function.Injective (πℓ'.app V))
        (hinvℓ' : ∀ V : Xℓ'.Opens, Set.range (πℓ'.app V) =
          {s | ∀ h : G, (ρℓ h).hom.appLE (πℓ' ⁻¹ᵁ V) (πℓ' ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπℓ' h]) s = s})
        (hopenℓ' : ∀ U : Mℓ.Opens, IsAffineOpen U → (∀ h : G, (ρℓ h).hom ⁻¹ᵁ U = U) → ∃ V : Xℓ'.Opens, IsAffineOpen V ∧ πℓ' ⁻¹ᵁ V = U)
        (πXℓ' : Xℓ' ⟶ Spec (CommRingCat.of 𝒪)) (hπXℓ' : πℓ' ≫ πXℓ' = fMℓ)
        (eXℓ : Xℓ' ⟶ 𝒴 ℓ) (heXℓiso : IsIso eXℓ) (heXℓ : eXℓ ≫ g ℓ = πXℓ'),
          πℓ' ≫ eXℓ = pℓ := by sorry
