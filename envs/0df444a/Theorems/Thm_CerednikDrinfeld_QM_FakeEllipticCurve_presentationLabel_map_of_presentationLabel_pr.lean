-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_presentationLabel_map_of_presentationLabel_pr
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.presentationLabel_map_of_presentationLabel_pr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/ef75b14d-f028-549f-9e74-6bd1cc08a446
-- title:
--   Labelled presentations of R-points are stable under base change
-- statement:
--   The statement is set inside the Čerednik–Drinfeld fine-level frame, whose data and hypotheses fall into the following groups.
--
--   *Arithmetic base.* Primes $r$ and $\bar r$ with $\bar r \neq r$, a level $N$ with $N \neq 0$, squarefree, divisible by neither $r$ nor $\bar r$; a complete discrete valuation ring $\mathcal O$ of characteristic zero with uniformiser $\pi$ (irreducible, $\mathcal O$ being $\pi$-adically complete), residue field of cardinality $r$ and $(r)=(\pi)$, with fraction field $K_0$ of characteristic zero; an $\mathcal O$-algebra $Onr$ which is a domain of characteristic zero, $\pi$-adically complete, with $(\pi Onr)$ maximal, every element of $Onr$ satisfying a monic $\mathcal O$-polynomial congruence modulo $\pi$, every monic polynomial of positive degree over $Onr$ having a root modulo $\pi$, and an $\mathcal O$-automorphism $Fr$ of $Onr$ with $Fr(x)\equiv x^{r}$ modulo $\pi$ (so $Onr$ plays the role of the maximal unramified extension and $Fr$ of the Frobenius); a homomorphism $vdet$ from $\mathrm{GL}_2(K_0)$ to $\mathbb Z$ (written multiplicatively) characterised by $vdet(g)=n$ if and only if $\det g$ is a unit of $\mathcal O$ times $\pi^{n}$.
--
--   *Indefinite quaternion side and moduli.* Rationals $a,b$ with $\mathbb H[\mathbb Q,a,b]$ indefinite and ramified exactly at $r$ and $\bar r$, a maximal order $\Lambda$ containing all rational integers ($h\Lambda\mathbb Z$); a scheme $\mathcal X$ over $\operatorname{Spec}\mathcal O$ with a point map $pt$ and the hypothesis $h\mathcal X$ that it is a coarse moduli space for fake elliptic curves of level $N$ (isomorphism-invariance, compatibility with pullback, surjectivity and injectivity on geometric points, and the universal property); an integer $n \geq 3$ prime to $r$, to $\bar r$ and to $N$, a fine moduli scheme $M$ over $\mathcal O$ for fake elliptic curves with full level-$n$ structure with point map $ptF$ ($hM$), a group $G$ acting on $M$ by $\rho$ with labels $\chi : G \to \Lambda$ satisfying the level-twist axioms $h\rho$ (the action is over the base, twisting by $\chi(g)$ moves the point map by $\rho(g)$, and $\chi$ is multiplicative, surjective and injective modulo $n$); a forgetful map $p : M \to \mathcal X$ over $\mathcal O$, invariant under $\rho$ and compatible with the two point maps; the Hecke tower data $\mathcal Y_\ell, g_\ell, ptT$ for primes $\ell \neq r,\bar r$ with the coarse moduli property $h\mathcal Y$ for extra level-$\ell$ structures, the two degeneracy maps $d_0,d_1$ over $\mathcal O$ and their moduli descriptions; the Atkin–Lehner correspondences $ar, arbar$ on $\mathcal X$ over $\mathcal O$ inducing the Atkin–Lehner quotients at $r$ and at $\bar r$ on points.
--
--   *Definite quaternion side.* Rationals $a_1,b_1$ with $\mathbb H[\mathbb Q,a_1,b_1]$ definite and ramified exactly at $\bar r$; a maximal order $\Lambda_1$ and an Eichler order $R_1$ of level $N$ inside it; an idele $n_1$ in the prime Hecke set of $R_1$ at $r$ with $\mathrm{meetOrder}(R_1,n_1)$ Eichler of level $Nr$; an injective $\mathbb Q$-algebra map $\iota_0$ of $\mathbb H[\mathbb Q,a_1,b_1]$ into $M_2(K_0)$; a place $v$ of $\mathbb Q$ above $r$; the group $\Gamma t$ of units of $\mathbb H[\mathbb Q,a_1,b_1]$ described by $h\Gamma t$ as the away-from-$v$ unit group of $R_1$; elements $s_\ell$ and ideles $sf_\ell$ for each prime $\ell \neq r,\bar r$ whose local behaviour, Hecke membership and reduced norm $\ell$ are prescribed by $hs$, with $\Gamma t_\ell = \Gamma t \cap s_\ell \Gamma t s_\ell^{-1}$; and an element $wbar$ of reduced norm $\bar r$ normalising $\Gamma t$.
--
--   *The reduction datum at $r$.* An order coordinate $coord$ on $\Lambda$ ($hcoord$: additive, unital, multiplicative in the twisted sense, injective, dense and trace-compatible); a fake elliptic curve $A_0$ over $Onr/\pi$, a formal $\mathcal O_D$-module $X_0$ of height $4$ over $Onr/\pi$, formal coordinates $\theta_0$ of $A_0$ in two variables with $hA_0$ asserting that $A_0$ is formally the module $X_0$ via $coord$; endomorphisms $e(\gamma), e'(\gamma)$ of $A_0$ for $\gamma \in \Gamma t$ over the base with degrees $\deg\gamma$, and the hypotheses $hE1$ (each pair is an isogeny pair of degree $r^{\deg\gamma}$ preserving the level), $hE1mul$, $hE1sc$ (multiplicativity and scalars, up to powers of $r$), $hE1'$ (only scalars act by integers up to powers of $r$), $hE2$ (the action on the formal module is, after conjugation by a single $g \in \mathrm{GL}_2(K_0)$, given by $\iota_0(\gamma)$ up to a power of $r$), $hE3$ (labels in $\Lambda$ for the action on a full level-$n$ structure, multiplicative and scalar-compatible modulo $n$), $hE4$ (every $r$-power isogeny preserving the level on a geometric fibre comes from some $\gamma$), and the group $hE5a$–$hE5e$ for an auxiliary order $R_2 \leq R_1$ with $r$-power denominators, furnishing endomorphisms $\hat e$ of $A_0$ additive, $\Lambda$-equivariant, level-preserving, multiplicative, compatible with integers and with the star involution and reduced norm, compatible with $e$ up to $r$-powers, and jointly uniformised with $e$ on the formal module.
--
--   *The Drinfeld-side moduli package.* A ring map $\iota : \mathbb{Z}_{r^2}\text{-Witt} \to Onr$, a special formal $\mathcal O_D$-module $\Phi$ of height $4$ over $Onr/r$, a moduli package $MD$ over $Onr$ which is a Zariski sheaf, a rigidification classifying map $\eta$ and the hypotheses $h\eta$ (injectivity on admissible rigidified objects up to isomorphism, naturality, local surjectivity), a faithful matrix realisation $E_0$ of the centraliser of the action of $\Phi$ with the integrality property $hE_0$; the comparison $eD$ of the Drinfeld functor $G$ of $MD$ with the product of $\operatorname{Spec}Onr$ and the formal upper half plane $\Omega$ over $K_0$, natural ($hnatD$), bijective ($hbijD$), with first component the structure map ($hfstD$), translating the $\mathrm{GL}_2(K_0)$-action into the twisted action of $vdet$ ($hGLD$) and the $\pi$-translation into the Frobenius twist ($hPiD$, $hPiexD$).
--
--   *The dictionary.* A ring map $\kappa$ from $Onr/\pi$ to $Onr/r$ compatible with the quotient maps ($h\kappa$), an isogeny $\beta_0$ from $\Phi$ to $X_0 \otimes \kappa$ of height $4n_0$; a full level-$n$ structure $P_0$ on $A_0$; the Atkin–Lehner data at $\bar r$ on $A_0$, namely $A_{0w}$ with maps $aw, aw', bw, bw'$, the hypotheses $hALw$ (Atkin–Lehner quotient at $\bar r$ via $aw,aw'$), $hBSw$, $hBSwlev$ ($bw,bw'$ an isogeny pair of degree $r^{kw}$ preserving the level) and $hJOINTw$ (the composite $aw \gg bw$ acts on the formal module as $\iota_0(wbar)$ up to a power of $r$, simultaneously with the $\Gamma t$-uniformisation); a map $\Xi$ assigning to each rigidified fake elliptic curve over a Noetherian $\mathcal O$-algebra $B$ with $\pi$ nilpotent a point of $G$ of $MD$, subject to $h\Xi leg$ (over connected $B$ the structure leg of $\Xi$ is a Frobenius twist of $\psi$), $h\Xi nat$ (naturality under base change of rigidified curves), $h\Xi iso$ (invariance under isomorphisms of rigidified curves matching the rigidification data up to $r$-powers) and $h\Xi def$ (the explicit description of $\Xi$ through a rigid transport of $\theta_0$ along $\kappa,\beta_0$ with exponent $j \leq 1$ and an admissible rigidified object); a matrix $g_0 \in \mathrm{GL}_2(K_0)$ and the equivariance hypotheses $heq\Gamma$ and $heqW$, which say that translating a rigidification by $e(\gamma)$, respectively passing to the Atkin–Lehner quotient at $\bar r$ with a matching comparison of rigidifications, corresponds under $\Xi$ to the action of $r^{c} g_0 \iota_0(\gamma) g_0^{-1}$, respectively $r^{c}g_0\iota_0(wbar)g_0^{-1}$, for some $c \in \mathbb Z$.
--
--   *The representing functor.* A Noetherian $\mathcal O$-algebra $C$ with $\pi$ nilpotent, an $\mathcal O$-algebra map $\chi_C : Onr \to C$, a functor $PR$ on $C$-algebras with a point map $ptR$ sending a full level-$n$ structure together with a rigidification relative to $A_0$ (for the leg $\psi_S$ forced to equal the composite of $\chi_C$ with $C \to S$) to an element of $PR(S)$, subject to $hR2$ (naturality of $ptR$ under $C$-algebra maps compatible with the level structures and rigidifications), $hR3s$ (every element of $PR(S)$ is of this form), $hR3i$ (two data with the same image over a connected $S$ are related by an isomorphism of level structures and a comparison of rigidifications up to $r$-powers) and $hR1$ (the converse: such a comparison forces equality of the images).
--
--   Finally, let $S$ and $S'$ be Noetherian $C$-algebras with compatible $\mathcal O$-structures, $\varphi : S \to S'$ a $C$-algebra map, $x \in PR(S)$, $g \in G$ and $j \in \{0,1\}$.
--
--   The assertion is the implication between two statements of the same shape. Suppose that $\pi$ is nilpotent in $S$ and that there exist an $\mathcal O$-algebra map $\psi_S : Onr \to S$ equal to the composite of $\chi_C$ with the structure map $C \to S$, a fake elliptic curve with full level-$n$ structure $u$ over $S$ and a rigidification $\rho$ of $u.1$ relative to $A_0$ along $\psi_S$ such that: $ptR(u,\rho) = x$; there is a full level-$n$ structure $P_n$ on $u.1$ which is the normalised level transport of $P_0$ along $\rho$ (in the sense of `IsNormLevelTransport` for $Fr,\theta_0,\kappa,\beta_0,\Phi,\iota,coord$) with the given level structure $u.2.P$ equal to the push-forward of $P_n$ by the action of $\chi(g)$; and the structure leg of $\Xi(u.1,\rho)$ equals the $(-j)$-th Frobenius twist of $\psi_S$. Then the same holds over $S'$ for the image $PR(\varphi)(x)$, with the same $g$ and the same $j$: $\pi$ is nilpotent in $S'$, and there exist $\psi_{S'}$ equal to the composite of $\chi_C$ with $C \to S'$, a fake elliptic curve with full level-$n$ structure $u'$ over $S'$ and a rigidification $\rho'$ of $u'.1$ along $\psi_{S'}$ with $ptR(u',\rho') = PR(\varphi)(x)$, a full level-$n$ structure $P_n'$ on $u'.1$ which is the normalised level transport of $P_0$ along $\rho'$ with $u'.2.P$ the push-forward of $P_n'$ by the action of $\chi(g)$, and the structure leg of $\Xi(u'.1,\rho')$ equal to the $(-j)$-th Frobenius twist of $\psi_{S'}$.
--
--   This is the base-change compatibility of labelled presentations of points of the relative space representing rigidified fake elliptic curves with full level-$n$ structure: a presentation with label $(g,j)$ of an $S$-point propagates to the induced $S'$-point along any $C$-algebra map $S \to S'$. It feeds the naturality clause of the labelling statement [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_label_natural_iff_exists_ptR_eq_of_rigidifiedToG_connInj_pr`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_label_natural_iff_exists_ptR_eq_of_rigidifiedToG_connInj_pr), and is proved by pulling back the presenting triple (via `WithFullLevel.exists_isPullback_levelIff`, `Rigidification.exists_isPullbackVia_of_isPullbackVia` and `FullLevel.exists_comp_eq_specMap_comp_of_isPullbackVia`), transporting the normalisation along the base change with `Rigidification.isNormLevelTransport_of_isPullbackVia_of_isNoetherianRing_frame`, and using the naturality of $\Xi$ for the leg.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_presentationLabel_map_of_presentationLabel_pr.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_AlgFunctorConst
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMRigidificationLevel
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.presentationLabel_map_of_presentationLabel_pr

    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N) (hN : Squarefree N)

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)), FakeEllipticCurve Λ N S → SchemeHomOver s f)
    (h𝒳 : IsCoarseModuli Λ N 𝒳 f pt)

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (hrbarn : ¬ rbar ∣ n) (hnN : Nat.Coprime n N)
    (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (G : Type) [Group G] (ρ : G →* Aut M) (χ : G → ↥Λ) (hρ : IsLevelTwistAction Λ N n M fM ptF G ρ χ)

    (p : M ⟶ 𝒳) (hp : p ≫ f = fM) (hρp : ∀ h : G, (ρ h).hom ≫ p = p)
    (hp_pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N n S),
      (ptF S s u).1 ≫ p = (pt S s u.1).1)
    (𝒴 : HeckeTower.AwayPrime r rbar → Scheme.{0}) (g : ∀ ℓ : HeckeTower.AwayPrime r rbar, 𝒴 ℓ ⟶ Spec (CommRingCat.of 𝒪))
    (ptT : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S → SchemeHomOver s (g ℓ))
    (h𝒴 : ∀ ℓ : HeckeTower.AwayPrime r rbar, IsCoarseModuliT Λ N (ℓ.1 : ℕ) (𝒴 ℓ) (g ℓ) (ptT ℓ))
    (d₀ d₁ : ∀ ℓ : HeckeTower.AwayPrime r rbar, 𝒴 ℓ ⟶ 𝒳) (hd₀f : ∀ ℓ, d₀ ℓ ≫ f = g ℓ) (hd₁f : ∀ ℓ, d₁ ℓ ≫ f = g ℓ)
    (hd₀ : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S), (ptT ℓ S s u).1 ≫ d₀ ℓ = (pt S s u.1).1)
    (hd₁ : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S) (d : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsLevelIsogeny (ℓ.1 : ℕ) u d → (ptT ℓ S s u).1 ≫ d₁ ℓ = (pt S s d).1)

    (ar arbar : 𝒳 ⟶ 𝒳) (harf : ar ≫ f = f) (harbarf : arbar ≫ f = f)
    (har : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient r E E' → (pt S s E).1 ≫ ar = (pt S s E').1)
    (harbar : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient rbar E E' → (pt S s E).1 ≫ arbar = (pt S s E').1)

    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) rbar)
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (n₁ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₁ : n₁ ∈ primeHeckeSet R₁ r)
    (hS₁ : IsEichlerOrder (meetOrder R₁ n₁) (N * r))
    (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀) (hι₀ : Function.Injective ι₀)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)

    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓt : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt ↔ x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v)
    (s : HeckeTower.AwayPrime r rbar → (ℍ[ℚ, a₁, b₁])ˣ)
    (sf : HeckeTower.AwayPrime r rbar → (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs : ∀ ℓ : HeckeTower.AwayPrime r rbar,
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s ℓ : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * (sf ℓ)⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₁ (meetOrder R₁ n₁) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₁ n₁) (ℓ.1 : ℕ)) ∧
      nrd (s ℓ : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ))
    (Γtℓ : HeckeTower.AwayPrime r rbar → Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓtℓ : ∀ ℓ : HeckeTower.AwayPrime r rbar, Γtℓ ℓ = Γt ⊓ Γt.map (MulAut.conj (s ℓ)).toMonoidHom)

    (wbar : (ℍ[ℚ, a₁, b₁])ˣ) (hwbar : nrd (wbar : ℍ[ℚ, a₁, b₁]) = ((rbar : ℕ) : ℚ) ∧ ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt → wbar * x * wbar⁻¹ ∈ Γt)

    (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)

    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (X₀ : FormalODModule r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (e e' : ↥Γt → (A₀.A ⟶ A₀.A)) (he : ∀ γ, e γ ≫ A₀.f = A₀.f) (deg : ↥Γt → ℕ)

    (hX₀ : X₀.HasHeight 4) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)

    (hE1 :
      (∀ γ : ↥Γt, FakeEllipticCurve.IsIsogenyPair (r ^ deg γ) A₀ A₀ (e γ) (e' γ) ∧ FakeEllipticCurve.PreservesLevel A₀ A₀ (e γ) (he γ)))
    (hE1mul :
      (∀ γ γ' : ↥Γt, ∃ i j : ℕ,
          e (γ * γ') ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = e γ' ≫ e γ ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩))
    (hE1sc :
      (∀ (γ : ↥Γt) (c : ℤ), ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = (c : ℚ) • (1 : ℍ[ℚ, a₁, b₁]) →
          ∃ i : ℕ, e γ ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = A₀.act ⟨((c * ((r ^ i : ℕ) : ℤ) : ℤ) : ℚ), hΛℤ _⟩))

    (hE1' :
      (∀ (γ : ↥Γt), (∃ (i c : ℕ), 0 < c ∧ e γ ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = A₀.act ⟨((c : ℤ) : ℚ), hΛℤ _⟩) →
          ∃ c : ℚ, ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = c • (1 : ℍ[ℚ, a₁, b₁])))

    (hE2 :
      (∀ E₀ : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀, Function.Injective E₀ →
        ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, ∀ γ : ↥Γt, ∃ (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kγ : ℤ),
          (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
              J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
              θ₀ B' (fun i => MvFormalGroup.nilEval m ((ε : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                mapPt (e γ) (he γ) (θ₀ B' s)) ∧
          E₀ ε = ((r : K₀) ^ kγ) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))))

    (hE3 :
      (∀ P₀ : A₀.FullLevel n, ∃ lab : ↥Γt → ↥Λ,
        (∀ γ : ↥Γt, mapPt (e γ) (he γ) P₀.P = pushPt (A₀.act (lab γ)) (A₀.act_over (lab γ)) P₀.P) ∧
        (∀ γ γ' : ↥Γt, ∃ y : ↥Λ, (lab (γ * γ') : ℍ[ℚ, a, b]) - (lab γ' : ℍ[ℚ, a, b]) * (lab γ : ℍ[ℚ, a, b]) = (n : ℚ) • (y : ℍ[ℚ, a, b])) ∧
        (∀ (γ : ↥Γt) (c : ℤ), ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) = (c : ℚ) • (1 : ℍ[ℚ, a₁, b₁]) →
            ∃ y : ↥Λ, (lab γ : ℍ[ℚ, a, b]) - (c : ℚ) • (1 : ℍ[ℚ, a, b]) = (n : ℚ) • (y : ℍ[ℚ, a, b]))))

    (hE4 :
      (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) k]
          (A : FakeEllipticCurve Λ N k) (gA : A.A ⟶ A₀.A),
          FakeEllipticCurve.IsPullbackVia (algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) k) A₀ A gA →
          (∀ (φ ψ : A.A ⟶ A.A) (d : ℕ) (hφ : φ ≫ A.f = A.f),
              FakeEllipticCurve.IsIsogenyPair (r ^ d) A A φ ψ → FakeEllipticCurve.PreservesLevel A A φ hφ →
              ∃ (γ : ↥Γt) (i j : ℕ), φ ≫ A.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ ≫ gA = gA ≫ e γ ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩)))

    (R₂ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₂ : R₂ ≤ R₁) (hR₂o : IsOrder R₂)
          (hR₂r : ∀ x : ↥R₁, ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • (x : ℍ[ℚ, a₁, b₁]) ∈ R₂)
          (ê : ↥R₂ → (A₀.A ⟶ A₀.A)) (hê : ∀ x, ê x ≫ A₀.f = A₀.f)

        (hE5a : ∀ x : ↥R₂,
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))) (P Q : SchemeHomOver t A₀.f),
              mapPt (ê x) (hê x) (A₀.L.mul t P Q) = A₀.L.mul t (mapPt (ê x) (hê x) P) (mapPt (ê x) (hê x) Q)) ∧
          (∀ m : ↥Λ, A₀.act m ≫ ê x = ê x ≫ A₀.act m) ∧
          FakeEllipticCurve.PreservesLevel A₀ A₀ (ê x) (hê x))

        (hE5b1 : ∀ h : (1 : ℍ[ℚ, a₁, b₁]) ∈ R₂, ê ⟨1, h⟩ = 𝟙 A₀.A)
        (hE5b2 : ∀ (x y : ↥R₂) (h : (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ∈ R₂),
            ê ⟨(x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]), h⟩ = ê y ≫ ê x)
        (hE5b3 : ∀ (m : ℤ) (h : ((m : ℚ) : ℍ[ℚ, a₁, b₁]) ∈ R₂), ê ⟨((m : ℚ) : ℍ[ℚ, a₁, b₁]), h⟩ = A₀.act ⟨((m : ℤ) : ℚ), hΛℤ m⟩)

        (hE5c : ∀ (x y : ↥R₂) (nx : ℤ), (y : ℍ[ℚ, a₁, b₁]) = star (x : ℍ[ℚ, a₁, b₁]) → nrd (x : ℍ[ℚ, a₁, b₁]) = (nx : ℚ) →
            ê y ≫ ê x = A₀.act ⟨((nx : ℤ) : ℚ), hΛℤ nx⟩)

        (hE5d : ∀ (γ : ↥Γt) (x : ↥R₂) (k : ℕ),
            (x : ℍ[ℚ, a₁, b₁]) = ((r ^ k : ℕ) : ℚ) • ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) →
            ∃ i j : ℕ, e γ ≫ A₀.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ê x ≫ A₀.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩)

        (hE5e : ∀ E₀ : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀, Function.Injective E₀ →
          ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀,
            (∀ γ : ↥Γt, ∃ (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kγ : ℤ),
              (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
                  J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
                  θ₀ B' (fun i => MvFormalGroup.nilEval m ((ε : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                    mapPt (e γ) (he γ) (θ₀ B' s)) ∧
              E₀ ε = ((r : K₀) ^ kγ) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
                ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))) ∧
            (∀ x : ↥R₂, ∃ (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kx : ℤ),
              (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
                  J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
                  θ₀ B' (fun i => MvFormalGroup.nilEval m ((ε : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                    mapPt (ê x) (hê x) (θ₀ B' s)) ∧
              E₀ ε = ((r : K₀) ^ kx) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ (x : ℍ[ℚ, a₁, b₁]) *
                ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))))

    (ι : Zp2 r →+* Onr)
    (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r Onr)).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (MD : ModuliPackage.{0, 0} r Onr) (hMD : MD.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → MD.obj B ψ hB)
    (hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B))
          (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
          (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr →+* B) (ψ' : Onr →+* B')
          (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
          (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          η B' ψ' hB' (t.map f) = MD.map hB hB' f hf (η B ψ hB t)) ∧
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)) (m : MD.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (r : L)),
              ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  MD.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
    (hE₀ : Function.Injective E₀ ∧
      ∃ m : ℕ,
        (∀ A : Matrix (Fin 2) (Fin 2) 𝒪, ∃ e, E₀ e = (r : K₀) ^ m • A.map (algebraMap 𝒪 K₀)) ∧
        (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪, (r : K₀) ^ m • E₀ e = A.map (algebraMap 𝒪 K₀)))

      (eD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (ModuliPackage.G 𝒪 MD).obj B → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B)

      (hnatD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
          (φ : B →ₐ[𝒪] B') (x : (ModuliPackage.G 𝒪 MD).obj B), eD B' hB' ((ModuliPackage.G 𝒪 MD).map φ x) = (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ (eD B hB x))

      (hbijD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)), Function.Bijective (eD B hB))

      (hfstD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (ModuliPackage.G 𝒪 MD).obj B), (eD B hB x).1 = x.ψ)

      (hGLD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x x' : (ModuliPackage.G 𝒪 MD).obj B),
          ModuliPackage.G.IsActBy ι Φ η Fr E₀ g x x' ↔ OmegaNr.IsTwistedAct π Onr Fr vdet B g (eD B hB x) (eD B hB x'))

      (hPiD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x x' : (ModuliPackage.G 𝒪 MD).obj B),
          ModuliPackage.G.IsPiTranslate ι Φ η Fr x x' → eD B hB x' = (frobTwist Onr Fr 1 (eD B hB x).1, (eD B hB x).2))

      (hPiexD : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (x : (ModuliPackage.G 𝒪 MD).obj B), ∃ x' : (ModuliPackage.G 𝒪 MD).obj B, ModuliPackage.G.IsPiTranslate ι Φ η Fr x x')

    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ pIdeal r Onr))
    (hκ : κ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π})) = Ideal.Quotient.mk (pIdeal r Onr))
    (n₀ : ℕ) (β₀ : Series (Onr ⧸ pIdeal r Onr)) (hβ₀ : FormalODModule.IsIsogenyOfHeight Φ (X₀.map κ) β₀ (4 * n₀))

    (P₀ : A₀.FullLevel n)

    (A₀w : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (aw : A₀.A ⟶ A₀w.A) (haw : aw ≫ A₀w.f = A₀.f) (aw' : A₀w.A ⟶ A₀.A) (haw' : aw' ≫ A₀.f = A₀w.f)
    (kw : ℕ) (bw : A₀w.A ⟶ A₀.A) (hbw : bw ≫ A₀.f = A₀w.f) (bw' : A₀.A ⟶ A₀w.A) (habw : (aw ≫ bw) ≫ A₀.f = A₀.f)
    (hALw : FakeEllipticCurve.IsAtkinLehnerQuotientVia rbar A₀ A₀w aw haw aw' haw')
    (hBSw : FakeEllipticCurve.IsIsogenyPair (r ^ kw) A₀w A₀ bw bw') (hBSwlev : FakeEllipticCurve.PreservesLevel A₀w A₀ bw hbw)
    (hJOINTw :
      (∀ E₀ : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀, Function.Injective E₀ →
        ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀,
          (∀ γ : ↥Γt, ∃ (ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (kγ : ℤ),
          (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
              J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B', (∀ i, s i ∈ J) →
              θ₀ B' (fun i => MvFormalGroup.nilEval m ((ε : MvFormalGroup.End X₀.F).toPowerSeries i) s) =
                mapPt (e γ) (he γ) (θ₀ B' s)) ∧
          E₀ ε = ((r : K₀) ^ kγ) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((γ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))) ∧

          (∃ (εw : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd}))) (k_w : ℤ),
              (∀ (B' : Type) [CommRing B'] [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'] (J : Ideal B') (m : ℕ),
                J ^ (m + 1) = ⊥ → ∀ v : Fin 2 → B', (∀ i, v i ∈ J) →
                θ₀ B' (fun i => MvFormalGroup.nilEval m ((εw : MvFormalGroup.End X₀.F).toPowerSeries i) v) =
                  mapPt (aw ≫ bw) habw (θ₀ B' v)) ∧
              E₀ εw = ((r : K₀) ^ k_w) • ((g : Matrix (Fin 2) (Fin 2) K₀) * ι₀ ((wbar : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) *
                ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀)))))

    (Ξ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B),
        IsNilpotent (algebraMap 𝒪 B π) → FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ → ModuliPackage.GPoint 𝒪 MD B)

    (hΞleg :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ), ∃ k : ℤ, (Ξ B ψ hB x).ψ = frobTwist Onr Fr k ψ))

    (hΞnat :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B']
          (φ : B →ₐ[𝒪] B') (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (x' : FakeEllipticCurve.RigidifiedCurve r π A₀ B' (φ.comp ψ))
          (g : x'.1.A ⟶ x.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* B') x.1 x'.1 g),
          FakeEllipticCurve.Rigidification.IsPullbackVia φ g hg x.2 x'.2 → Ξ B' (φ.comp ψ) hB' x' = (Ξ B ψ hB x).map φ))

    (hΞiso :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (x x' : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (i : x.1.A ≅ x'.1.A) (hi : i.hom ≫ x'.1.f = x.1.f),
          FakeEllipticCurve.IsoVia x.1 x'.1 i hi →
          (∃ (ib : x.2.Eb.A ⟶ x'.2.Eb.A) (_ : ib ≫ x'.2.gb = x.2.gb ≫ i.hom) (_ : ib ≫ x'.2.Eb.f = x.2.Eb.f)
            (uA : x'.2.Ab.A ⟶ x.2.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) x.2.Ab x'.2.Ab uA) (_ : uA ≫ x.2.gA = x'.2.gA)
            (i₁ j₁ : ℕ),
            ib ≫ x'.2.φ ≫ uA ≫ x.2.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = x.2.φ ≫ x.2.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
            Ξ B ψ hB x = Ξ B ψ hB x'))

    (hΞdef :
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (hBr : IsNilpotent ((r : ℕ) : B))
          (x : FakeEllipticCurve.RigidifiedCurve r π A₀ B ψ) (X : FormalODModule r B) (θ : RelativeGroupLaw.FormalCoordinates x.1.f 2),
          x.1.IsFormalModuleVia coord X θ →
          ∃ (j : ℕ) (t : Rigidified r Φ B), j ≤ 1 ∧ t.X = X ∧
            FakeEllipticCurve.Rigidification.IsRigTransport θ₀ κ β₀ x.2 θ j t ∧
            t.IsAdmissible ι ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) ∧
            Ξ B ψ hB x = ⟨frobTwist Onr Fr (-(j : ℤ)) ψ, hBr, η B ((frobTwist Onr Fr (-(j : ℤ)) ψ : Onr →ₐ[𝒪] B) : Onr →+* B) hBr t⟩))

    (g₀ : Matrix.GeneralLinearGroup (Fin 2) K₀)

      (heqΓ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (E : FakeEllipticCurve Λ N B) (ρ ρ' : FakeEllipticCurve.Rigidification r π A₀ ψ E) (γ : ↥Γt),
          FakeEllipticCurve.Rigidification.IsTranslateBy hΛℤ (e γ) ρ ρ' →
            ∃ c : ℤ,
              ModuliPackage.G.IsActBy ι Φ η Fr E₀
                ((Units.map (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)).toMonoidHom
                  (Units.mk0 (r : K₀) (Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero))) ^ c *
                  (g₀ * Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀) (γ : (ℍ[ℚ, a₁, b₁])ˣ) * g₀⁻¹))
                (Ξ B ψ hB ⟨E, ρ⟩) (Ξ B ψ hB ⟨E, ρ'⟩))

      (heqW : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hconn : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
          (hrbarB : IsUnit ((rbar : ℕ) : B))
          (E Ef : FakeEllipticCurve Λ N B)
          (q : E.A ⟶ Ef.A) (hq : q ≫ Ef.f = E.f) (q' : Ef.A ⟶ E.A) (hq' : q' ≫ E.f = Ef.f),
          FakeEllipticCurve.IsAtkinLehnerQuotientVia rbar E Ef q hq q' hq' →
          ∀ (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρf : FakeEllipticCurve.Rigidification r π A₀ ψ Ef),
          (∃ (qb : ρ.Eb.A ⟶ ρf.Eb.A) (_ : qb ≫ ρf.gb = ρ.gb ≫ q) (_ : qb ≫ ρf.Eb.f = ρ.Eb.f)
            (uA : ρf.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρf.Ab uA) (_ : uA ≫ ρ.gA = ρf.gA)
            (ewb : ρ.Ab.A ⟶ ρ.Ab.A) (_ : ewb ≫ ρ.gA = ρ.gA ≫ (aw ≫ bw)) (_ : ewb ≫ ρ.Ab.f = ρ.Ab.f)
            (i j : ℕ),
            qb ≫ ρf.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ewb ≫ ρ.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
            ∃ c : ℤ,
              ModuliPackage.G.IsActBy ι Φ η Fr E₀
                ((Units.map (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)).toMonoidHom
                  (Units.mk0 (r : K₀) (Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero))) ^ c *
                  (g₀ * Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀) wbar * g₀⁻¹))
                (Ξ B ψ hB ⟨E, ρ⟩) (Ξ B ψ hB ⟨Ef, ρf⟩))

    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra 𝒪 C] (hCπ : IsNilpotent (algebraMap 𝒪 C π)) (χC : Onr →ₐ[𝒪] C)
    (PR : CerednikDrinfeld.FormalOmega.AlgFunctor C)
    (ptR : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
        (ψS : Onr →ₐ[𝒪] S) (_ : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
        (u : FakeEllipticCurve.WithFullLevel Λ N n S), FakeEllipticCurve.Rigidification r π A₀ ψS u.1 →
          PR.obj S)

    (hR2 : (∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          [CommRing S'] [Algebra C S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S'] (φ : S →ₐ[C] S')
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
          (hψS' : (φ.restrictScalars 𝒪).comp ψS = (IsScalarTower.toAlgHom 𝒪 C S').comp χC)
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
          (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1)
          (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((φ.restrictScalars 𝒪).comp ψS) u'.1)
          (g : u'.1.A ⟶ u.1.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : S →+* S') u.1 u'.1 g),
          (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom (φ : S →+* S')) ≫ (u.2.P).1 →
          FakeEllipticCurve.Rigidification.IsPullbackVia (φ.restrictScalars 𝒪) g hg ρ ρ' →
            PR.map φ (ptR S ψS hψS u ρ) = ptR S' ((φ.restrictScalars 𝒪).comp ψS) hψS' u' ρ'))

    (hR3s : (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
          (z : PR.obj S),
          ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n S) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1), ptR S ψS hψS u ρ = z))
    (hR3i : (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
          (hSc : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1)
          (u u' : FakeEllipticCurve.WithFullLevel Λ N n S)
          (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψS u'.1),
          ptR S ψS hψS u ρ = ptR S ψS hψS u' ρ' →
            ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi ∧
              ∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
              (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
              (i₁ j₁ : ℕ),
              ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩))

    (hR1 : (∀ (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
          (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
          (u u' : FakeEllipticCurve.WithFullLevel Λ N n S)
          (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1) (ρ' : FakeEllipticCurve.Rigidification r π A₀ ψS u'.1)
          (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f),
          FakeEllipticCurve.WithFullLevel.IsoVia u u' i hi →
          (∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
              (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
              (i₁ j₁ : ℕ),
              ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩) →
            ptR S ψS hψS u ρ = ptR S ψS hψS u' ρ'))
    (S S' : Type) [CommRing S] [Algebra C S] [IsNoetherianRing S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    [CommRing S'] [Algebra C S'] [IsNoetherianRing S'] [Algebra 𝒪 S'] [IsScalarTower 𝒪 C S']
    (φ : S →ₐ[C] S') (x : PR.obj S) (g : G) (j : Fin 2)
    :
      (∃ (hS : IsNilpotent (algebraMap 𝒪 S π)) (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp χC)
            (u : FakeEllipticCurve.WithFullLevel Λ N n S) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1),
            ptR S ψS hψS u ρ = x ∧
            (∃ Pn : u.1.FullLevel n, FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ρ Pn ∧
              u.2.P = pushPt (u.1.act (χ g)) (u.1.act_over (χ g)) Pn.P) ∧
            (Ξ S ψS hS ⟨u.1, ρ⟩).ψ = frobTwist Onr Fr (-(j : ℤ)) ψS) →
        (∃ (hS : IsNilpotent (algebraMap 𝒪 S' π)) (ψS : Onr →ₐ[𝒪] S') (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S').comp χC)
            (u : FakeEllipticCurve.WithFullLevel Λ N n S') (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1),
            ptR S' ψS hψS u ρ = (PR.map φ x) ∧
            (∃ Pn : u.1.FullLevel n, FakeEllipticCurve.Rigidification.IsNormLevelTransport Fr θ₀ κ β₀ Φ ι coord P₀ ρ Pn ∧
              u.2.P = pushPt (u.1.act (χ g)) (u.1.act_over (χ g)) Pn.P) ∧
            (Ξ S' ψS hS ⟨u.1, ρ⟩).ψ = frobTwist Onr Fr (-(j : ℤ)) ψS) := by sorry
