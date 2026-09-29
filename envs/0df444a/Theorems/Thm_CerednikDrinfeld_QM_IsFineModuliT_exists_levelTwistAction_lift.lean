-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuliT_exists_levelTwistAction_lift
-- name    : CerednikDrinfeld.QM.IsFineModuliT.exists_levelTwistAction_lift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/d9cf9c28-b6e3-5b7b-bf1d-746d7ff32288
-- title:
--   Level-twisting action lifts to the fine scheme of triples
-- statement:
--   Fix primes $r \ne \bar r$ and a squarefree $N \ne 0$ divisible by neither, and let $\mathcal O$ be a characteristic-zero domain which is a discrete valuation ring, complete for the adic topology of $(\pi)$ with $\pi$ irreducible, with residue ring of cardinality $r$ and $(r) = (\pi)$. Let $\mathbb H[\mathbb Q,a,b]$ be indefinite ($0<a$ or $0<b$) and, at each height-one prime $v$ of $\mathcal O_{\mathbb Q}$, a division algebra after completion exactly when $v$ contains $r$ or $\bar r$; let $\Lambda$ be a maximal order in it. Let $n \ge 3$ be prime to $r$, $\bar r$ and $N$. Assume given: a scheme $M$ over $\operatorname{Spec}\mathcal O$ with point assignment $\mathrm{ptF}$ on pairs (fake elliptic curve $E$ with $\Lambda$-action and level-$N$ data, full level-$n$ structure) which is a fine moduli (isomorphism-invariance, base-change compatibility, bijectivity on $S$-points); separatedness of $M \to \operatorname{Spec}\mathcal O$; the property that every finite subset of $M$ lies in an affine open; a group $G$ with $\rho : G \to \operatorname{Aut} M$ and $\chi : G \to \Lambda$ forming a level-twisting action ($\rho$ is over the base, $\mathrm{ptF}$ of a $\chi(h)$-twist is $\mathrm{ptF}$ followed by $\rho(h)$, and $\chi$ is multiplicative, surjective and injective modulo $n$); for every prime $\ell \notin \{r,\bar r\}$ a coarse moduli $\mathcal Y_\ell$ over $\mathcal O$ for pairs (curve, extra level-$\ell$ structure); and, for one such $\ell$, a fine moduli $M_\ell$ over $\mathcal O$ for triples $(E,P,C)$ with point assignment $\mathrm{ptF}_\ell$, together with morphisms $\pi_\ell : M_\ell \to M$ and $p_\ell : M_\ell \to \mathcal Y_\ell$ over $\mathcal O$ compatible with the point assignments (forgetting $C$, respectively forgetting $P$). The conclusion asserts the existence of a group homomorphism $\rho_\ell : G \to \operatorname{Aut} M_\ell$ such that for every $h \in G$: $\rho_\ell(h)$ is a morphism over $\operatorname{Spec}\mathcal O$, $\pi_\ell \circ \rho_\ell(h) = \rho(h) \circ \pi_\ell$, $p_\ell \circ \rho_\ell(h) = p_\ell$, and $\rho_\ell(h)$ twists level structures: whenever $(u,C)$ and $(u',C')$ are triples over a ring $S$ with $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal O$ and $e : u.A \cong u'.A$ is an isomorphism over $S$ exhibiting $u'$ as the $\chi(h)$-twist of $u$ (i.e. $e$ respects the relative group law, commutes with the $\Lambda$-actions, matches the level-$N$ data in the sense that a point factors through $u.\mathrm{lev}$ iff its image factors through $u'.\mathrm{lev}$, and carries the $\chi(h)$-translate of the full level-$n$ point of $u$ to that of $u'$), and $e$ identifies the extra level-$\ell$ subschemes (a point factors through $C.\mathrm{levK}$ iff its image factors through $C'.\mathrm{levK}$), then $\mathrm{ptF}_\ell(S,s,u',C') = \mathrm{ptF}_\ell(S,s,u,C)$ followed by $\rho_\ell(h)$.
--
--   This is the statement that the action of $(\Lambda/n\Lambda)^\times$ by twisting the auxiliary full level-$n$ structure, present on the fine moduli scheme of pairs, lifts canonically to the fine moduli scheme of triples with extra level-$\ell$ structure, commuting with the forgetful map to $M$ and acting trivially over the coarse moduli scheme of pairs $(E,C)$. It is used in the construction of the level-$\ell$ coarse moduli scheme as a quotient of $M_\ell$ by this action, via [`CerednikDrinfeld.QM.IsFineModuli.exists_isFineModuliT_quotient_presentation_of_isSeparated`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_isFineModuliT_quotient_presentation_of_isSeparated).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuliT_exists_levelTwistAction_lift.lean

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

theorem CerednikDrinfeld.QM.IsFineModuliT.exists_levelTwistAction_lift

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
          (C : u.1.ExtraLevel (ℓ.1 : ℕ)), (ptFℓ S s u C).1 ≫ pℓ = (ptT ℓ S s ⟨u.1, C⟩).1) :
    ∃ (ρℓ : G →* Aut Mℓ) (hρℓf : ∀ h : G, (ρℓ h).hom ≫ fMℓ = fMℓ)
      (hρℓπ : ∀ h : G, (ρℓ h).hom ≫ πℓ = πℓ ≫ (ρ h).hom) (hρℓp : ∀ h : G, (ρℓ h).hom ≫ pℓ = pℓ),
      ∀ (h : G) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
          (u u' : FakeEllipticCurve.WithFullLevel Λ N n S) (C : u.1.ExtraLevel (ℓ.1 : ℕ)) (C' : u'.1.ExtraLevel (ℓ.1 : ℕ))
          (e : u.1.A ≅ u'.1.A) (he : e.hom ≫ u'.1.f = u.1.f),
          FakeEllipticCurve.WithFullLevel.IsTwistVia (χ h) u u' e he →
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
              FactorsThrough C.levK P ↔ FactorsThrough C'.levK (mapPt e.hom he P)) →
            (ptFℓ S s u' C').1 = (ptFℓ S s u C).1 ≫ (ρℓ h).hom := by sorry
