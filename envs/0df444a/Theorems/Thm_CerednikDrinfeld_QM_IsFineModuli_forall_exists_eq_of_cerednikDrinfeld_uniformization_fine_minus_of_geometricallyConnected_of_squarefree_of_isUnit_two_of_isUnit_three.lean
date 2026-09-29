-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_forall_exists_eq_of_cerednikDrinfeld_uniformization_fine_minus_of_geometricallyConnected_of_squarefree_of_isUnit_two_of_isUnit_three
-- name    : CerednikDrinfeld.QM.IsFineModuli.forall_exists_eq_of_cerednikDrinfeld_uniformization_fine_minus_of_geometricallyConnected_of_squarefree_of_isUnit_two_of_isUnit_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/285f1968-f1d4-5625-9f05-56cc3fefb857
-- title:
--   Surjectivity of the Čerednik–Drinfeld parametrisation on geometric points
-- statement:
--   Setting. Fix primes $r$ and $\bar r$ with $\bar r \neq r$ and a non-zero level $N$ with $r \nmid N$, $\bar r \nmid N$ and $N$ squarefree.
--
--   Coefficient rings. $\mathcal O$ is a commutative domain of characteristic zero which is a discrete valuation ring, in which $2$ and $3$ are units; $\pi \in \mathcal O$ is irreducible, $\mathcal O$ is $\pi$-adically complete, the residue ring $\mathcal O/(\pi)$ has exactly $r$ elements, and $(r) = (\pi)$ as ideals of $\mathcal O$; $K_0$ is a fraction field of $\mathcal O$, of characteristic zero. Next, $Onr$ is a commutative domain of characteristic zero over $\mathcal O$, equipped with an $\mathcal O$-algebra automorphism $Fr$, such that $Onr$ is $\pi$-adically complete, $(\pi Onr)$ is maximal, every element of $Onr$ satisfies a monic polynomial over $\mathcal O$ modulo $\pi$, every monic polynomial over $Onr$ of positive degree has a root modulo $\pi$, and $Fr(x) \equiv x^r \pmod{\pi}$ for all $x$; thus $Onr$ plays the role of the integers of the maximal unramified extension with its Frobenius. Finally $vdet : \mathrm{GL}_2(K_0) \to \mathbb Z$ (written multiplicatively) satisfies `hvdet`: $vdet(g) = n$ precisely when $\det g = u\pi^n$ for some $u \in \mathcal O^\times$, i.e. $vdet$ is the $\pi$-adic valuation of the determinant.
--
--   The indefinite side. $a, b \in \mathbb Q$ are such that `hB` holds: $0 < a$ or $0 < b$, and for a finite place $v$ of $\mathbb Q$ the algebra $\mathbb H[\mathbb Q, a, b] \otimes_{\mathbb Q} \mathbb Q_v$ is a division algebra exactly when $v$ lies above $r$ or above $\bar r$; $\Lambda$ is a maximal order in $\mathbb H[\mathbb Q, a, b]$. A scheme $\mathcal X$ with $f : \mathcal X \to \operatorname{Spec}\mathcal O$ and point maps $pt$ is a coarse moduli space for fake elliptic curves with $\Lambda$-action and level-$N$ structure over $\mathcal O$-algebras, in the sense of `IsCoarseModuli` (invariance under isomorphism, compatibility with base change, bijectivity of $pt$ on geometric points over algebraically closed fields, and the universal property among such point systems). The generic fibre, that is the second projection of the pullback of $f$ along $\operatorname{Spec} K_0 \to \operatorname{Spec}\mathcal O$, is assumed geometrically reduced and geometrically connected.
--
--   Fine level. $n \geq 3$ with $r \nmid n$, $\bar r \nmid n$ and $\gcd(n, N) = 1$; $M$ with $fM : M \to \operatorname{Spec}\mathcal O$ and $ptF$ is a fine moduli space for fake elliptic curves with level-$N$ structure together with a full level-$n$ structure, in the sense of `IsFineModuli` (invariance under isomorphism, compatibility with base change, and bijectivity of $ptF$ on $S$-points for every commutative ring $S$). A group $G$ acts through $\rho : G \to \operatorname{Aut} M$ with labels $\chi : G \to \Lambda$, and `hρ` (`IsLevelTwistAction`) requires: each $\rho(g)$ lies over the base; twisting a full level-$n$ structure by $\chi(g)$ transports moduli points along $\rho(g)$; and $\chi$ is, modulo $n$, multiplicative, sends $1$ to $1$, hits every class invertible modulo $n$, and is injective modulo $n$.
--
--   Comparison and Hecke data. A morphism $p : M \to \mathcal X$ satisfies $p$ followed by $f$ equals $fM$, is $G$-invariant ($\rho(h)$ followed by $p$ equals $p$), and carries $ptF$-points to $pt$-points of the underlying fake elliptic curve. For every prime $\ell \notin \{r, \bar r\}$, a scheme $\mathcal Y_\ell$ with $g_\ell$ and points $ptT_\ell$ is a coarse moduli space for fake elliptic curves with an extra level-$\ell$ subgroup scheme (`IsCoarseModuliT`), and $d_0(\ell), d_1(\ell) : \mathcal Y_\ell \to \mathcal X$ lie over $g_\ell$, with $d_0$ forgetting the extra structure and $d_1$ computing the quotient along any level-$\ell$ isogeny. Two endomorphisms $ar, arbar$ of $\mathcal X$ over the base realise the Atkin–Lehner involutions at $r$ and at $\bar r$ on moduli points, in the sense that they transport $pt(E)$ to $pt(E')$ whenever $E'$ is an Atkin–Lehner quotient of $E$ at $r$, respectively at $\bar r$.
--
--   The definite side. $a_1, b_1 \in \mathbb Q$ are such that `hdef` holds: $a_1 < 0$, $b_1 < 0$, and $\mathbb H[\mathbb Q, a_1, b_1] \otimes_{\mathbb Q} \mathbb Q_v$ is a division algebra exactly at the place above $\bar r$. Here $\Lambda_1$ is a maximal order, $R_1 \leq \Lambda_1$ an Eichler order of level $N$ (an intersection of two maximal orders of relative index $N$), $n_1$ a finite idele in $primeHeckeSet\ R_1\ r$, and the order $meetOrder\ R_1\ n_1 = R_1 \cap n_1 R_1 n_1^{-1}$ is Eichler of level $N r$. Further, $\iota_0$ is an injective $\mathbb Q$-algebra map $\mathbb H[\mathbb Q, a_1, b_1] \to M_2(K_0)$, and $v$ is a height-one prime of $\mathbb Z$ containing $r$. The subgroup $\Gamma t$ of $\mathbb H[\mathbb Q, a_1, b_1]^\times$ is characterised by $\Gamma t = awayUnits\ R_1\ v$, the units lying in the local unit boxes of $R_1$ at all primes other than $v$. For each prime $\ell \notin \{r, \bar r\}$, elements $s_\ell \in \mathbb H[\mathbb Q, a_1, b_1]^\times$ and finite ideles $sf_\ell$ satisfy `hs`: $sf_\ell$ has component $s_\ell$ at every prime not above $r$ and component $1$ at the primes above $r$; the product of the diagonal idele of the scalar $\ell$ with $sf_\ell^{-1}$ lies in $levelHeckeUSet\ \Lambda_1\ (meetOrder\ R_1\ n_1)\ \ell$ if $\ell \mid N$ and in $primeHeckeSet\ (meetOrder\ R_1\ n_1)\ \ell$ otherwise; and $\mathrm{nrd}(s_\ell) = \ell$. The groups $\Gamma t_\ell$ are defined by $\Gamma t_\ell = \Gamma t \cap s_\ell \Gamma t s_\ell^{-1}$. An element $\bar w$ of $\mathbb H[\mathbb Q, a_1, b_1]^\times$ has reduced norm $\bar r$ and normalises $\Gamma t$, and `hwR` provides $k$ with $r^k \bar w \in R_1$. A homomorphism $\theta t : \Gamma t \to G$ is given.
--
--   The parametrisation. For every $\mathcal O$-algebra $B$ in which $\pi$ is nilpotent, $\Theta_f$ assigns to each triple consisting of an $\mathcal O$-algebra map $Onr \to B$, a Deligne datum in $(\Omega\,K_0\,\pi)(B)$ and an element of $G$, a $B$-point of $M$ over $\mathcal O$, that is a morphism $\operatorname{Spec} B \to M$ composing with $fM$ to the structure morphism. Five groups of hypotheses constrain $\Theta_f$: `hnat`, naturality of $\Theta_f$ in $B$ along $\mathcal O$-algebra maps between $\pi$-nilpotent algebras; `hG`, that $\rho(h)$ applied to $\Theta_f(x, g h)$ equals $\Theta_f(x, g)$; `hinv`, that whenever $x'$ is obtained from $x$ by the twisted action `OmegaNr.IsTwistedAct` of $\iota_0(\gamma)$ for $\gamma \in \Gamma t$ — i.e. the $Onr$-component of $x'$ is the $Fr^{-vdet(\iota_0\gamma)}$-twist of that of $x$ and the Deligne datum of $x'$ is the pullback of that of $x$ under $\iota_0(\gamma)^{-1}$ — one has $\Theta_f(x', \theta t(\gamma) g) = \Theta_f(x, g)$; `het`, a formal étaleness property: for a surjective $\mathcal O$-algebra map $p : B \to B_0$ between $\pi$-nilpotent algebras whose kernel has square zero, every $B$-point $y$ of $M$ whose image in $B_0$ equals $\Theta_f(x_0)$ admits a unique lift $x$ of $x_0$ with $\Theta_f(x) = y$; and `hfib`, the description of the fibres of $\Theta_f$ over an algebraically closed $\pi$-nilpotent field $k$: $\Theta_f((\psi, P), g) = \Theta_f((\psi', P'), g')$ holds if and only if there is $\gamma \in \Gamma t$ with $g' = \theta t(\gamma) g$, with $P'$ the pullback of $P$ along $\iota_0(\gamma)^{-1}$ in the sense of `DeligneDatum.IsPullback`, and with $\psi'(y) = (\psi \circ Fr^{-vdet(\iota_0\gamma)})(y)$ for every $y \in Onr$ that is fixed by $Fr^{vdet(\iota_0 z)}$ for all scalar elements $z \in \Gamma t$ (those with $z = c \cdot 1$ for some $c \in \mathbb Q$) satisfying $\theta t(z) = 1$.
--
--   Conclusion. For every algebraically closed field $k$ which is an $\mathcal O$-algebra in which the image of $\pi$ is nilpotent, every $\mathcal O$-algebra homomorphism $\psi : Onr \to k$, and every $k$-point $y$ of $M$ over $\mathcal O$, there exist a Deligne datum $P \in (\Omega\,K_0\,\pi)(k)$ and an element $g \in G$ with $\Theta_f\big((\psi, P), g\big) = y$. In particular the surjectivity holds with the $Onr$-component $\psi$ prescribed in advance.
--
--   This is the surjectivity half of the Čerednik–Drinfeld uniformisation at the level of geometric points: the formal parametrisation $\Theta_f$ of the fine moduli scheme $M$ of fake elliptic curves with full level-$n$ structure, built from the $\pi$-adic upper half plane, the unramified base $Onr$ and the twisting group $G$, reaches every geometric point of $M$ over a $\pi$-nilpotent algebraically closed field. It feeds the construction of the full fine-level uniformisation with Atkin–Lehner data, which combines it with the injectivity statement supplied by the fibre description.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_forall_exists_eq_of_cerednikDrinfeld_uniformization_fine_minus_of_geometricallyConnected_of_squarefree_of_isUnit_two_of_isUnit_three.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_AlgFunctorConst
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.FormalOmega NeronModelInfra

theorem CerednikDrinfeld.QM.IsFineModuli.forall_exists_eq_of_cerednikDrinfeld_uniformization_fine_minus_of_geometricallyConnected_of_squarefree_of_isUnit_two_of_isUnit_three

    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N) (hN : Squarefree N)

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (h2 : IsUnit ((2 : ℕ) : 𝒪)) (h3 : IsUnit ((3 : ℕ) : 𝒪))
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

    [hgr : GeometricallyReduced (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 K₀))))]
    [hgc : GeometricallyConnected (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 K₀))))]

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
    (hwR : ∃ k : ℕ, ((r ^ k : ℕ) : ℚ) • ((wbar : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) ∈ R₁)

    (θt : ↥Γt →* G)
    (Θf : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → (Scheme.nilpPoints fM).obj B)

    (hnat :
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
          Θf B' hB' ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints fM).map φ (Θf B hB x))

    (hG :
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g h : G),
          (Scheme.nilpPoints.mapHom fM fM (ρ h).hom (hρ.over_base h)).app B (Θf B hB (x, g * h)) = Θf B hB (x, g))

    (hinv :
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt)
          (x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g : G),
          OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ) x x' → Θf B hB (x', θt ⟨γ, hγ⟩ * g) = Θf B hB (x, g))

    (het :
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B₀ : Type) [CommRing B₀] [Algebra 𝒪 B₀] (p : B →ₐ[𝒪] B₀)
          (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB₀ : IsNilpotent (algebraMap 𝒪 B₀ π)),
          Function.Surjective p → (∀ s t : B, p s = 0 → p t = 0 → s * t = 0) →
          ∀ (x₀ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B₀) (y : (Scheme.nilpPoints fM).obj B), (Scheme.nilpPoints fM).map p y = Θf B₀ hB₀ x₀ →
            ∃! x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B, (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map p x = x₀ ∧ Θf B hB x = y)

    (hfib :
      ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)) (ψ : Onr →ₐ[𝒪] k),
          ∀ (ψ' : Onr →ₐ[𝒪] k) (P P' : (Omega K₀ π).obj k) (g g' : G),
            Θf k hk ((ψ, P), g) = Θf k hk ((ψ', P'), g') ↔
              ∃ (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt), g' = θt ⟨γ, hγ⟩ * g ∧
                DeligneDatum.IsPullback (K := K₀) (π := π) k ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ)⁻¹ P P' ∧
                ∀ y : Onr, (∀ (z : (ℍ[ℚ, a₁, b₁])ˣ) (hz : z ∈ Γt), (∃ c : ℚ, (z : ℍ[ℚ, a₁, b₁]) = c • (1 : ℍ[ℚ, a₁, b₁])) →
                    θt ⟨z, hz⟩ = 1 → (Fr ^ Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z))) y = y) →
                  ψ' y = frobTwist Onr Fr (- Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ))) ψ y)
    :
    ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)) (ψ : Onr →ₐ[𝒪] k)
      (y : (Scheme.nilpPoints fM).obj k), ∃ (P : (Omega K₀ π).obj k) (g : G), Θf k hk ((ψ, P), g) = y := by sorry
