-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_existsUnique_factor_of_cerednikDrinfeld_uniformization_fine
-- name    : CerednikDrinfeld.QM.IsFineModuli.existsUnique_factor_of_cerednikDrinfeld_uniformization_fine
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/8cae1b5e-f766-5d02-9786-5e5757c18ba8
-- title:
--   Unique factorisation of invariant families through Theta_f
-- statement:
--   The statement is set in the Čerednik–Drinfeld frame, whose data fall into the following groups.
--
--   **Arithmetic base.** Two distinct primes $r$ and $\bar r$ (`hrr`) and a nonzero natural number $N$ divisible by neither (`hrN`, `hrbarN`). A characteristic-zero domain $\mathcal O$ which is a discrete valuation ring (`hdvr`) with irreducible element $\pi$ (`hπ`), $\pi$-adically complete (`hcomplete`), with residue ring of cardinality $r$ (`hres`) and $(r) = (\pi)$ (`hunr`), together with its field of fractions $K_0$, of characteristic zero. A characteristic-zero domain $O^{\mathrm{nr}}$ (`Onr`), an $\mathcal O$-algebra, with an $\mathcal O$-algebra automorphism $\mathrm{Fr}$, such that $O^{\mathrm{nr}}$ is $\pi$-adically complete (`hOnr_complete`), $\pi O^{\mathrm{nr}}$ is maximal (`hOnr_max`), every element satisfies a monic polynomial over $\mathcal O$ modulo $\pi$ (`hOnr_alg`), every monic polynomial over $O^{\mathrm{nr}}$ of positive degree has a root modulo $\pi$ (`hOnr_closed`), and $\mathrm{Fr}(x) \equiv x^{r} \pmod{\pi}$ for all $x$ (`hFr`). Finally a homomorphism $\mathrm{vdet} : \mathrm{GL}_2(K_0) \to \mathbb Z$ (written multiplicatively) which by `hvdet` satisfies $\mathrm{vdet}(g) = n$ exactly when $\det g = u\,\pi^{n}$ for some $u \in \mathcal O^{\times}$, i.e. $\mathrm{vdet}$ is the $\pi$-adic valuation of the determinant.
--
--   **Indefinite quaternion algebra and moduli data.** Rationals $a, b$ with `hB` asserting that $\mathbb H[\mathbb Q, a, b]$ is indefinite ($0 < a$ or $0 < b$) and that, for a finite place $v$ of $\mathbb Q$, every nonzero element of $\mathbb H[\mathbb Q,a,b] \otimes_{\mathbb Q} \mathbb Q_v$ is a unit precisely when $v$ lies over $r$ or over $\bar r$; a maximal order $\Lambda$ (`hΛ`: an order, maximal among orders). A scheme $\mathcal X$ with a morphism $f$ to $\operatorname{Spec}\mathcal O$ and an assignment `pt` sending a commutative ring $S$, a morphism $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal O$ and an object of `FakeEllipticCurve Λ N S` (an abelian scheme of relative fibre dimension two over $S$ carrying an action of $\Lambda$ subject to a trace condition, together with a level-$N$ subscheme) to a morphism $\operatorname{Spec} S \to \mathcal X$ over $s$; `h𝒳` is the coarse moduli property `IsCoarseModuli` (invariance of `pt` under isomorphism, compatibility with base change along ring maps, bijectivity of `pt` on points with values in algebraically closed fields, and the universal property towards any other such family). An integer $n \ge 3$ (`hn`) prime to $r$, $\bar r$ (`hrn`, `hrbarn`) and to $N$ (`hnN`); a scheme $M$ with $f_M : M \to \operatorname{Spec}\mathcal O$ and an assignment `ptF` on full level-$n$ structures `FakeEllipticCurve.WithFullLevel Λ N n S`, with `hM` the fine moduli property `IsFineModuli` (isomorphism-invariance, compatibility with base change, and bijectivity of `ptF` for every commutative ring $S$). A group $G$, a homomorphism $\rho : G \to \operatorname{Aut} M$ and a labelling $\chi : G \to \Lambda$ with `hρ` the property `IsLevelTwistAction` (each $\rho(g)$ is a morphism over the base; twisting a full level structure by $\chi(g)$ corresponds to composing `ptF` with $\rho(g)$; and the labels behave multiplicatively, surjectively and injectively modulo $n$).
--
--   **Forgetful morphism, Hecke tower and Atkin–Lehner involutions.** A morphism $p : M \to \mathcal X$ over $\operatorname{Spec}\mathcal O$ (`hp`), invariant under $\rho$ (`hρp`) and carrying `ptF` to `pt` (`hp_pt`). For each prime $\ell$ distinct from $r$ and $\bar r$, a scheme $\mathcal Y_\ell$ over $\operatorname{Spec}\mathcal O$ with an assignment `ptT` on extra level-$\ell$ structures which is a coarse moduli family (`h𝒴`, the clauses of `IsCoarseModuliT`), and two degeneracy morphisms $d_0(\ell), d_1(\ell) : \mathcal Y_\ell \to \mathcal X$ over the base (`hd₀f`, `hd₁f`) such that $d_0$ forgets the extra level (`hd₀`) and $d_1$ sends a point to the target of any level-$\ell$ isogeny out of it (`hd₁`). Two morphisms $a_r, a_{\bar r} : \mathcal X \to \mathcal X$ over the base (`harf`, `harbarf`) inducing on moduli points the Atkin–Lehner quotients at $r$ and at $\bar r$ (`har`, `harbar`).
--
--   **Definite quaternion algebra and the uniformising group.** Rationals $a_1, b_1$ with `hdef` asserting $a_1 < 0$, $b_1 < 0$ and that $\mathbb H[\mathbb Q, a_1, b_1] \otimes_{\mathbb Q} \mathbb Q_v$ is a division algebra exactly for $v$ over $\bar r$; a maximal order $\Lambda_1$ and an Eichler order $R_1$ of level $N$ (`hR₁`: an intersection of two maximal orders of relative index $N$) contained in $\Lambda_1$ (`hRΛ₁`); a finite-adelic unit $n_1$ in `primeHeckeSet R₁ r` (`hn₁`) such that `meetOrder R₁ n₁`, the intersection of $R_1$ with its conjugate by $n_1$, is Eichler of level $N r$ (`hS₁`); an injective $\mathbb Q$-algebra embedding $\iota_0 : \mathbb H[\mathbb Q,a_1,b_1] \to M_2(K_0)$ (`hι₀`); a height-one prime $v$ of $\mathcal O_{\mathbb Q}$ containing $r$ (`hv`). A subgroup $\Gamma_t$ of $\mathbb H[\mathbb Q,a_1,b_1]^{\times}$ which by `hΓt` consists exactly of the units lying in [`CerednikDrinfeld.CosetGraph.awayUnits R₁ v`](def/CerednikDrinfeld_CosetGraphAtPrime.html#L37), i.e. whose image at every finite place $w \ne v$ lies in the group generated by the local box units of $R_1$ at $w$. Families $s$ and $sf$ indexed by the primes $\ell \notin \{r,\bar r\}$, of units of the algebra and of its finite adelisation, with `hs` asserting for each $\ell$ four clauses: $sf_\ell$ is the image of $s_\ell$ at every finite place not over $r$; $sf_\ell = 1$ at the places over $r$; the product of the diagonal image of $\ell$ with $sf_\ell^{-1}$ lies in `levelHeckeUSet Λ₁ (meetOrder R₁ n₁) ℓ` if $\ell \mid N$ and in `primeHeckeSet (meetOrder R₁ n₁) ℓ` otherwise; and $\mathrm{nrd}(s_\ell) = \ell$. Subgroups $\Gamma_{t,\ell}$ given by `hΓtℓ` as $\Gamma_t \cap s_\ell \Gamma_t s_\ell^{-1}$. A unit $\bar w$ with `hwbar` asserting $\mathrm{nrd}(\bar w) = \bar r$ and that $\bar w$ normalises $\Gamma_t$.
--
--   **The uniformisation map.** A group homomorphism $\theta_t : \Gamma_t \to G$, and a family $\Theta_f$ which, for every $\mathcal O$-algebra $B$ in which $\pi$ is nilpotent, maps the set $\bigl((O^{\mathrm{nr}} \to_{\mathcal O} B) \times \mathrm{DeligneDatum}_{K_0,\pi}(B)\bigr) \times G$ — the value at $B$ of the product of the functor corepresented by $O^{\mathrm{nr}}$, the functor `Omega K₀ π` of Deligne data (a choice of $B$-submodule of $B \otimes_{\mathcal O} M$ for each full lattice $M \subset K_0^2$, with invertible quotient, monotone, homothety-equivariant and nondegenerate at every prime of $B$), and the constant functor $G$ — to the set of morphisms $\operatorname{Spec} B \to M$ over $\operatorname{Spec}\mathcal O$, i.e. to $(\mathtt{Scheme.nilpPoints } f_M).obj\, B$. The hypotheses on $\Theta_f$ are: `hnat`, naturality in $B$ along $\mathcal O$-algebra maps; `hG`, that for all $g, h \in G$ the natural transformation induced by the automorphism $\rho(h)$ of $M$ over the base carries $\Theta_f(x, g h)$ to $\Theta_f(x, g)$; `hinv`, that for $\gamma \in \Gamma_t$ and $x, x'$ related by `OmegaNr.IsTwistedAct` for the matrix $\iota_0(\gamma)$ (that is, the algebra map component of $x'$ is that of $x$ precomposed with $\mathrm{Fr}^{-\mathrm{vdet}(\iota_0(\gamma))}$, and the Deligne datum of $x'$ is the pullback of that of $x$ along $\iota_0(\gamma)^{-1}$) one has $\Theta_f(x', \theta_t(\gamma) g) = \Theta_f(x, g)$; `het`, the unique infinitesimal lifting property: for a surjective $\mathcal O$-algebra map $p : B \to B_0$ between rings in which $\pi$ is nilpotent whose kernel has square zero, and for $x_0$ over $B_0$ and a $B$-point $y$ of $M$ whose image in $B_0$ is $\Theta_f(x_0)$, there is a unique $x$ over $B$ with $x \mapsto x_0$ and $\Theta_f(x) = y$; and `hgeom`, the description of geometric points: for every algebraically closed field $k$ in which $\pi$ becomes nilpotent and every $\psi : O^{\mathrm{nr}} \to k$, every $k$-point of $M$ is of the form $\Theta_f((\psi, P), g)$, and $\Theta_f((\psi, P), g) = \Theta_f((\psi', P'), g')$ holds if and only if there is $\gamma \in \Gamma_t$ with $g' = \theta_t(\gamma) g$, with $P'$ the pullback of $P$ along $\iota_0(\gamma)^{-1}$, and with $\psi'(y) = (\psi \circ \mathrm{Fr}^{-\mathrm{vdet}(\iota_0(\gamma))})(y)$ for every $y \in O^{\mathrm{nr}}$ that is fixed by $\mathrm{Fr}^{\mathrm{vdet}(\iota_0(z))}$ for all scalar $z \in \Gamma_t$ with $\theta_t(z) = 1$.
--
--   **Conclusion.** Under these hypotheses, $\Theta_f$ has the following universal property. Let $T$ be a scheme, $t : T \to \operatorname{Spec}\mathcal O$ a morphism, and let $\rho'$ assign to every $\mathcal O$-algebra $B$ in which $\pi$ is nilpotent a map from $\bigl((O^{\mathrm{nr}} \to_{\mathcal O} B) \times \mathrm{DeligneDatum}_{K_0,\pi}(B)\bigr) \times G$ to the set of morphisms $\operatorname{Spec} B \to T$ over $\operatorname{Spec}\mathcal O$, such that $\rho'$ is natural in $B$ (for all $\mathcal O$-algebra maps $\varphi : B \to B'$ between such rings, $\rho'_{B'}(\varphi_*x) = \varphi_*(\rho'_B(x))$) and $\Gamma_t$-invariant in the same sense as `hinv` (for $\gamma \in \Gamma_t$ and $x, x'$ related by `OmegaNr.IsTwistedAct` for $\iota_0(\gamma)$, and all $g \in G$, $\rho'_B(x', \theta_t(\gamma) g) = \rho'_B(x, g)$). Then there exists a family $u$ assigning to every such $B$ a map from the morphisms $\operatorname{Spec} B \to M$ over $\operatorname{Spec}\mathcal O$ to the morphisms $\operatorname{Spec} B \to T$ over $\operatorname{Spec}\mathcal O$, with the three properties:
--
--   1. $u$ is natural in $B$: for all $\mathcal O$-algebra maps $\varphi : B \to B'$ between rings in which $\pi$ is nilpotent and all $B$-points $y$ of $M$, $u_{B'}(\varphi_* y) = \varphi_*(u_B(y))$;
--
--   2. $u$ factors $\rho'$ through $\Theta_f$: $u_B(\Theta_f(x)) = \rho'_B(x)$ for every such $B$ and every $x$;
--
--   3. $u$ is the only such family, pointwise: for every family $u'$ of the same shape which is natural in $B$ in the sense of 1 and satisfies $u'_B(\Theta_f(x)) = \rho'_B(x)$ for all $B$ and $x$, one has $u'_B(y) = u_B(y)$ for every such $B$ and every $B$-point $y$ of $M$.
--
--   This is the categorical-quotient, or effective descent, clause of the Čerednik–Drinfeld uniformisation of the fine moduli scheme of fake elliptic curves with full level-$n$ structure on $\pi$-nilpotent points: the map $\Theta_f$ from the product of the unramified-coefficient functor, the functor of Deligne data on the Bruhat–Tits tree and the twisting group $G$ exhibits the nilpotent-point functor of $f_M$ as the quotient by the action of $\Gamma_t$ through $\theta_t$. It is used in the construction of the uniformisation of the curve together with its level and Atkin–Lehner structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_existsUnique_factor_of_cerednikDrinfeld_uniformization_fine.lean

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

theorem CerednikDrinfeld.QM.IsFineModuli.existsUnique_factor_of_cerednikDrinfeld_uniformization_fine

    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N)

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

    (hgeom :
      ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)) (ψ : Onr →ₐ[𝒪] k),
          (∀ y : (Scheme.nilpPoints fM).obj k, ∃ (P : (Omega K₀ π).obj k) (g : G), Θf k hk ((ψ, P), g) = y) ∧
          ∀ (ψ' : Onr →ₐ[𝒪] k) (P P' : (Omega K₀ π).obj k) (g g' : G),
            Θf k hk ((ψ, P), g) = Θf k hk ((ψ', P'), g') ↔
              ∃ (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt), g' = θt ⟨γ, hγ⟩ * g ∧
                DeligneDatum.IsPullback (K := K₀) (π := π) k ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ)⁻¹ P P' ∧
                ∀ y : Onr, (∀ (z : (ℍ[ℚ, a₁, b₁])ˣ) (hz : z ∈ Γt), (∃ c : ℚ, (z : ℍ[ℚ, a₁, b₁]) = c • (1 : ℍ[ℚ, a₁, b₁])) →
                    θt ⟨z, hz⟩ = 1 → (Fr ^ Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z))) y = y) →
                  ψ' y = frobTwist Onr Fr (- Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ))) ψ y)
    :
    ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
          (ρ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → (Scheme.nilpPoints t).obj B),
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
            (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
            ρ' B' hB' ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints t).map φ (ρ' B hB x)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt)
            (x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g : G),
            OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ) x x' → ρ' B hB (x', θt ⟨γ, hγ⟩ * g) = ρ' B hB (x, g)) →
          ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints fM).obj B → (Scheme.nilpPoints t).obj B,
            (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
              (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints fM).obj B),
              u B' hB' ((Scheme.nilpPoints fM).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y)) ∧
            (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B), u B hB (Θf B hB x) = ρ' B hB x) ∧
            ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints fM).obj B → (Scheme.nilpPoints t).obj B,
              (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
                (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints fM).obj B),
                u' B' hB' ((Scheme.nilpPoints fM).map φ y) = (Scheme.nilpPoints t).map φ (u' B hB y)) →
              (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B), u' B hB (Θf B hB x) = ρ' B hB x) →
              ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints fM).obj B), u' B hB y = u B hB y := by sorry
