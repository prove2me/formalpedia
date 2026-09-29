-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuliT_apply_eq_apply_of_isPullback_of_frobTwist_eq_of_invariant
-- name    : CerednikDrinfeld.QM.IsFineModuliT.apply_eq_apply_of_isPullback_of_frobTwist_eq_of_invariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/a1303e7b-2d55-5859-a393-76bcb2230955
-- title:
--   Invariance at raised level of a twisted uniformising family
-- statement:
--   The statement is a conditional invariance assertion for a natural family $\rho'$ of points, formulated inside the full Čerednik–Drinfeld set‑up. The hypotheses fall into the following groups.
--
--   **Arithmetic base.** Primes $r$ and $\bar r$ with $\bar r \neq r$, and a positive integer $N$ which is squarefree and divisible by neither $r$ nor $\bar r$. A characteristic‑zero domain $\mathcal O$ which is a discrete valuation ring, an irreducible element $\pi \in \mathcal O$, $\mathcal O$ complete for the $\pi$‑adic topology, with $\operatorname{card}(\mathcal O/\pi) = r$ and $(r) = (\pi)$ as ideals of $\mathcal O$; a characteristic‑zero field $K_0$ which is a fraction field of $\mathcal O$.
--
--   **Unramified coefficients.** A characteristic‑zero domain $O^{\mathrm{nr}}$ over $\mathcal O$ with an $\mathcal O$‑algebra automorphism $\mathrm{Fr}$, such that $O^{\mathrm{nr}}$ is $\pi$‑adically complete, $\pi O^{\mathrm{nr}}$ is maximal, every element of $O^{\mathrm{nr}}$ satisfies some monic polynomial over $\mathcal O$ modulo $\pi$, every monic polynomial over $O^{\mathrm{nr}}$ of positive degree has a root modulo $\pi$, and $\mathrm{Fr}(x) \equiv x^{r} \pmod{\pi}$ for all $x$. A monoid homomorphism $\mathrm{vdet} : \mathrm{GL}_2(K_0) \to \mathbb Z$ (written multiplicatively) with the property that $\mathrm{vdet}(g) = n$ holds exactly when $\det g = u\,\pi^{n}$ for some unit $u$ of $\mathcal O$.
--
--   **Indefinite side and its moduli.** Rationals $a, b$ such that $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b r rbar`, i.e. $0 < a$ or $0 < b$, and a finite place of $\mathbb Q$ is ramified (the completed algebra being a division algebra) precisely when it lies above $r$ or above $\bar r$; a maximal order $\Lambda$. A scheme $\mathcal X$ with a morphism $f$ to $\operatorname{Spec}\mathcal O$ and a family $\mathrm{pt}$ attaching to each commutative ring $S$, each $\operatorname{Spec} S$‑point $s$ of $\operatorname{Spec}\mathcal O$ and each fake elliptic curve over $S$ with $\Lambda$‑action and level $N$ (the structure `FakeEllipticCurve`: an abelian scheme with commutative relative group law, two‑dimensional fibres, a $\Lambda$‑action compatible with the group law and satisfying a trace condition, together with level data; its fields are summarised here) a morphism to $\mathcal X$ over $s$; the hypothesis `h𝒳` asserts that this is a coarse moduli datum: invariance under isomorphism of curves, compatibility with base change along ring homomorphisms, surjectivity and injectivity up to isomorphism on points over algebraically closed fields, and the universal property among such families. Further, the generic fibre of $f$, namely the second projection of the pullback of $f$ along $\operatorname{Spec} K_0 \to \operatorname{Spec}\mathcal O$, is assumed geometrically reduced and geometrically connected.
--
--   **Fine level structure and level twists.** An integer $n \geq 3$ prime to $r$, to $\bar r$ and to $N$; a scheme $M$ over $\operatorname{Spec}\mathcal O$ with a family $\mathrm{ptF}$ on fake elliptic curves equipped with a full level‑$n$ structure, assumed (`hM`) to be a fine moduli datum: invariance under isomorphism, compatibility with base change, and bijectivity on $S$‑points for every commutative ring $S$. A group $G$ with a homomorphism $\rho : G \to \operatorname{Aut} M$ and a map $\chi : G \to \Lambda$ forming a level‑twist action (`hρ`): each $\rho(g)$ lies over the base, twisting a full level structure by $\chi(g)$ corresponds to composing the moduli point with $\rho(g)$, and $\chi$ is multiplicative, unital, surjective and injective modulo $n\Lambda$. A morphism $p : M \to \mathcal X$ over $\operatorname{Spec}\mathcal O$, invariant under all $\rho(h)$, and compatible with the two moduli families (forgetting the level‑$n$ structure).
--
--   **Hecke tower and Atkin–Lehner maps.** For each prime $\ell \notin \{r,\bar r\}$ a scheme $\mathcal Y_\ell$ over $\operatorname{Spec}\mathcal O$ with a family $\mathrm{ptT}_\ell$ on fake elliptic curves with extra level‑$\ell$ structure, assumed to be a coarse moduli datum in the same sense; two degeneracy morphisms $d_0^\ell, d_1^\ell : \mathcal Y_\ell \to \mathcal X$ over the base, where $d_0^\ell$ forgets the extra structure on moduli points and $d_1^\ell$ sends the point of $u$ to the point of any $d$ related to $u$ by an $\ell$‑level isogeny. Two endomorphisms $a_r, a_{\bar r}$ of $\mathcal X$ over $f$ which on moduli points realise the Atkin–Lehner quotient at $r$, respectively at $\bar r$.
--
--   **Definite side.** Rationals $a_1, b_1$ with $\mathbb H[\mathbb Q,a_1,b_1]$ definite ($a_1 < 0$, $b_1 < 0$) and ramified exactly at $\bar r$; a maximal order $\Lambda_1$, an Eichler order $R_1$ of level $N$ with $R_1 \le \Lambda_1$; an adelic unit $n_1$ in the prime Hecke set of $R_1$ at $r$ such that $\mathrm{meetOrder}\,R_1\,n_1 = R_1 \cap n_1 R_1 n_1^{-1}$ is an Eichler order of level $Nr$; an injective $\mathbb Q$‑algebra map $\iota_0 : \mathbb H[\mathbb Q,a_1,b_1] \to M_2(K_0)$; a height‑one prime $v$ of $\mathbb Z$ containing $r$. A subgroup $\Gamma_t$ of $\mathbb H[\mathbb Q,a_1,b_1]^{\times}$ whose elements are exactly those lying in $\mathrm{awayUnits}\,R_1\,v$, the intersection over all places $w \neq v$ of the preimages of the groups generated by the local unit boxes of $R_1$ at $w$. Elements $s_\ell \in \mathbb H[\mathbb Q,a_1,b_1]^{\times}$ and adelic units $\mathrm{sf}_\ell$, for each tower prime $\ell$, satisfying `hs`: $\mathrm{sf}_\ell$ has local component the diagonal image of $s_\ell$ at every place not above $r$ and component $1$ at places above $r$; the product of the diagonal idele of $\ell$ with $\mathrm{sf}_\ell^{-1}$ lies in $\mathrm{levelHeckeUSet}\,\Lambda_1\,(\mathrm{meetOrder}\,R_1\,n_1)\,\ell$ when $\ell \mid N$ and in the prime Hecke set of $\mathrm{meetOrder}\,R_1\,n_1$ at $\ell$ otherwise; and $\mathrm{nrd}(s_\ell) = \ell$. The groups $\Gamma_t(\ell) = \Gamma_t \cap s_\ell \Gamma_t s_\ell^{-1}$. An element $\bar w$ of reduced norm $\bar r$ normalising $\Gamma_t$. A group homomorphism $\theta_t : \Gamma_t \to G$.
--
--   **Uniformising families.** For each commutative $\mathcal O$‑algebra $B$ in which the image of $\pi$ is nilpotent, a map $\Theta_f$ from $(\operatorname{Hom}_{\mathcal O\text{-alg}}(O^{\mathrm{nr}},B) \times \Omega_{K_0,\pi}(B)) \times G$ to the set of $B$‑points of $M$ over $\operatorname{Spec}\mathcal O$, where $\Omega_{K_0,\pi}(B)$ is the set of Deligne data over $B$: families of $B$‑submodules $\mathrm{line}(M) \subseteq B \otimes_{\mathcal O} M$, one for each full $\mathcal O$‑lattice $M$ in $K_0^2$, with invertible quotient, monotone under inclusions of lattices, equivariant for scalar homotheties, and non‑degenerate at every prime of $B$. Similarly maps $\Theta_T^\ell$ into the $B$‑points of $\mathcal Y_\ell$, built on $\operatorname{Hom}_{\mathcal O\text{-alg}}(O^{\mathrm{nr}},-) \times \Omega_{K_0,\pi}$. The hypotheses on $\Theta_f$ are: naturality in $B$ (`hnat`); $G$‑equivariance (`hG`): pushing $\Theta_f(x, gh)$ along $\rho(h)$ gives $\Theta_f(x, g)$; invariance (`hinv`): for $\gamma \in \Gamma_t$ and $x, x'$ related by the twisted action of $\iota_0(\gamma)$ — that is, the $O^{\mathrm{nr}}$‑component of $x'$ is the $\mathrm{Fr}^{-\mathrm{vdet}(\iota_0\gamma)}$‑twist of that of $x$, and the Deligne datum of $x$ pulls back along $\iota_0(\gamma)^{-1}$ to that of $x'$ — one has $\Theta_f(x', \theta_t(\gamma)g) = \Theta_f(x,g)$; and a formal lifting property (`het`): for every surjection $p : B \to B_0$ of $\pi$‑nilpotent $\mathcal O$‑algebras whose kernel has square zero (stated as: any two elements annihilated by $p$ have product zero), every point $x_0$ over $B_0$ and every $B$‑point $y$ of $M$ whose image is $\Theta_f(x_0)$ admit a unique $x$ over $B$ with image $x_0$ and $\Theta_f(x) = y$.
--
--   **The family under consideration.** A tower prime $\ell \notin \{r,\bar r\}$; a scheme $T$ with a morphism $t$ to $\operatorname{Spec}\mathcal O$; and a family $\rho'$ assigning to each $\pi$‑nilpotent $\mathcal O$‑algebra $B$ a map from $(\operatorname{Hom}_{\mathcal O\text{-alg}}(O^{\mathrm{nr}},B) \times \Omega_{K_0,\pi}(B)) \times G$ to the $B$‑points of $T$ over $\operatorname{Spec}\mathcal O$, natural in $B$ (`hρnat`), and invariant (`hρinv`) under the twisted action of those $\gamma \in \Gamma_t$ which moreover lie in $\Gamma_t(\ell)$: if $x$ and $x'$ are related by the twisted action of $\iota_0(\gamma)$ in the above sense, then $\rho'(x', \theta_t(\gamma)g) = \rho'(x,g)$.
--
--   **Conclusion.** For every commutative $\mathcal O$‑algebra $C$ in which the image of $\pi$ is nilpotent, all points $x_1, x_2$ of $(\operatorname{Hom}_{\mathcal O\text{-alg}}(O^{\mathrm{nr}},C) \times \Omega_{K_0,\pi}(C)) \times G$, and every $\gamma \in \Gamma_t$ with $\gamma \in \Gamma_t(\ell)$, the following three conditions together imply $\rho'(x_2) = \rho'(x_1)$ over $C$:
--
--   1.
--
--   the Deligne datum of $x_2$ is the pullback of that of $x_1$ along $\iota_0(\gamma)^{-1}$: for every full lattice $M$, the line of $x_2$ at $M$ is the preimage, under the base‑changed action isomorphism for $\iota_0(\gamma)^{-1}$, of the line of $x_1$ at the translated lattice;
--
--   2.
--
--   for every $y \in O^{\mathrm{nr}}$ which is fixed by $\mathrm{Fr}^{\mathrm{vdet}(\iota_0 z)}$ for every $z \in \Gamma_t$ that is a rational scalar multiple of $1$ and satisfies $\theta_t(z) = 1$, the $\mathcal O$‑algebra map component of $x_2$ sends $y$ to the value at $y$ of the $\mathrm{Fr}^{-\mathrm{vdet}(\iota_0 \gamma)}$‑twist of the $\mathcal O$‑algebra map component of $x_1$, i.e. to $x_1$'s map applied to $\mathrm{Fr}^{-\mathrm{vdet}(\iota_0\gamma)}(y)$;
--
--   3.
--
--   the $G$‑components satisfy $(x_2)_2 = \theta_t(\gamma)\,(x_1)_2$.
--
--   This is an invariance step in the Čerednik–Drinfeld uniformisation of the Shimura curve attached to an indefinite quaternion algebra ramified at $r$ and $\bar r$: a family of points defined on the product of the corepresentable functor of $O^{\mathrm{nr}}$, Drinfeld's functor of Deligne data and the level‑twist group, invariant only under the smaller group $\Gamma_t \cap s_\ell\Gamma_t s_\ell^{-1}$ occurring at raised level, is shown to take equal values on points related by a $\Gamma_t(\ell)$‑translation, the agreement of the $O^{\mathrm{nr}}$‑components being required only on the subring fixed by the Frobenius powers coming from central elements of $\Gamma_t$ in the kernel of $\theta_t$. It is used in [`CerednikDrinfeld.QM.IsFineModuliT.existsUnique_factor_of_cerednikDrinfeld_uniformization_fine`](thm.html#CerednikDrinfeld.QM.IsFineModuliT.existsUnique_factor_of_cerednikDrinfeld_uniformization_fine), and relies on the descent of such families to the fixed subring and on the triviality of the action of scalar matrices on Deligne data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuliT_apply_eq_apply_of_isPullback_of_frobTwist_eq_of_invariant.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
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

theorem CerednikDrinfeld.QM.IsFineModuliT.apply_eq_apply_of_isPullback_of_frobTwist_eq_of_invariant

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

    (θt : ↥Γt →* G)
      (Θf : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → (Scheme.nilpPoints fM).obj B)
      (ΘT : ∀ ℓ : HeckeTower.AwayPrime r rbar, ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints (g ℓ)).obj B)

    (hnat :
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
          Θf B' hB' ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints fM).map φ (Θf B hB x)))

    (hG :
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g h : G),
          (Scheme.nilpPoints.mapHom fM fM (ρ h).hom (hρ.over_base h)).app B (Θf B hB (x, g * h)) = Θf B hB (x, g)))

    (hinv :
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt)
          (x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g : G),
          OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ) x x' → Θf B hB (x', θt ⟨γ, hγ⟩ * g) = Θf B hB (x, g)))

    (het :
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B₀ : Type) [CommRing B₀] [Algebra 𝒪 B₀] (p : B →ₐ[𝒪] B₀)
          (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB₀ : IsNilpotent (algebraMap 𝒪 B₀ π)),
          Function.Surjective p → (∀ s t : B, p s = 0 → p t = 0 → s * t = 0) →
          ∀ (x₀ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B₀) (y : (Scheme.nilpPoints fM).obj B), (Scheme.nilpPoints fM).map p y = Θf B₀ hB₀ x₀ →
            ∃! x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B, (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map p x = x₀ ∧ Θf B hB x = y))
    (ℓ : HeckeTower.AwayPrime r rbar)

    (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
    (ρ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → (Scheme.nilpPoints t).obj B)
    (hρnat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
      ρ' B' hB' ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints t).map φ (ρ' B hB x))
    (hρinv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt) (hγℓ : γ ∈ Γtℓ ℓ)
      (x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g : G),
      OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ) x x' → ρ' B hB (x', θt ⟨γ, hγ⟩ * g) = ρ' B hB (x, g))
    :
    ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π))
      (x₁ x₂ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj C) (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt) (hγℓ : γ ∈ Γtℓ ℓ),
      DeligneDatum.IsPullback (K := K₀) (π := π) C ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ)⁻¹ x₁.1.2 x₂.1.2 →
      (∀ y : Onr, (∀ (z : (ℍ[ℚ, a₁, b₁])ˣ) (hz : z ∈ Γt), (∃ c : ℚ, (z : ℍ[ℚ, a₁, b₁]) = c • (1 : ℍ[ℚ, a₁, b₁])) →
          θt ⟨z, hz⟩ = 1 → (Fr ^ Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z))) y = y) →
        (show Onr →ₐ[𝒪] C from x₂.1.1) y =
          frobTwist Onr Fr (- Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ))) (show Onr →ₐ[𝒪] C from x₁.1.1) y) →
      @Eq G x₂.2 (@HMul.hMul G G G _ (θt ⟨γ, hγ⟩) x₁.2) →
      ρ' C hC x₂ = ρ' C hC x₁ := by sorry
