-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_period_algEquiv_pt_iff_bcPlace_of_uniformizedHeckeCurve_of_two_mul_dvd
-- name    : CerednikDrinfeld.QM.exists_period_algEquiv_pt_iff_bcPlace_of_uniformizedHeckeCurve_of_two_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/60c0b5a1-010a-5ea0-bf8a-ac46b3f1fe44
-- title:
--   Complex uniformisation of the fake elliptic moduli curve
-- statement:
--   Arithmetic data. Fixed are natural numbers $N$ (nonzero), $q$ and $q'$, the latter two prime, with $q \nmid N$ (`hqN`), $q' \nmid N$ (`hq'N`) and $q' \neq q$ (`hqq'`), and a natural number $D$ divisible by $2Nqq'$ (`hD`). Rationals $a,b$ are given together with `hB : IsIndefiniteRamifiedExactlyAt a b q q'`, which asserts that $0 < a$ or $0 < b$, and that for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the algebra $\mathbb H[\mathbb Q,a,b] \otimes_{\mathbb Q} \mathbb Q_v$ has all nonzero elements invertible precisely when $q \in v$ or $q' \in v$. Further, $\Lambda \subseteq \mathbb H[\mathbb Q,a,b]$ is a $\mathbb Z$-submodule which is a maximal order (`hΛ`: it contains $1$, is closed under multiplication, spans over $\mathbb Q$, is finitely generated, and admits no strictly larger order), $N$ is squarefree (`hN`), and $R \subseteq \mathbb H[\mathbb Q,a,b]$ is an Eichler order of level $N$ (`hR`: $R$ is the intersection of two maximal orders, with relative index $N$ of the additive group of $R$ in that of the first), contained in $\Lambda$ (`hRΛ`). Finally $\iota : \mathbb H[\mathbb Q,a,b] \to M_2(\mathbb R)$ is an injective $\mathbb Q$-algebra map (`hι`).
--
--   The moduli package over $\mathbb Z[1/D]$. Here $\mathbb Z[1/D]$ denotes `Localization.Away ((D : ℕ) : ℤ)`. An integral scheme $X$ is given with a morphism $\pi_X : X \to \operatorname{Spec} \mathbb Z[1/D]$, together with an assignment `pt` which, for every commutative ring $S$, every $\operatorname{Spec} S$-point $s$ of $\operatorname{Spec}\mathbb Z[1/D]$ and every fake elliptic curve $E$ over $S$ of the project's type `FakeEllipticCurve Λ N S` (an abelian scheme over $S$ with commutative relative group law, two-dimensional fibres, an action `act` of $\Lambda$ by $S$-endomorphisms which is additive, satisfies $\mathrm{act}(xy) = \mathrm{act}(y)$ followed by $\mathrm{act}(x)$, and whose tangent traces are prescribed by reduced traces, together with the level-$N$ datum $\mathrm{lev}$), returns a point of $X$ over $s$, i.e. an element of `SchemeHomOver s πX`. The hypotheses on this package are: $\pi_X$ is smooth (`hsmooth`), proper (`hproper`) and smooth of relative dimension $1$ (`hsmooth1`); all geometric fibres are integral, in the form that for every algebraically closed field $k$ and every $k$-point $s$ of $\operatorname{Spec}\mathbb Z[1/D]$ the pullback of $\pi_X$ along $s$ is integral (`hgeom`); `pt` is constant on isomorphism classes in the sense of `FakeEllipticCurve.Iso` (`pt_iso`); `pt` commutes with base change, namely for a ring map $\varphi : S \to S'$ with $\operatorname{Spec}\varphi$ followed by $s$ equal to $s'$, and $E'$ a pullback of $E$ along $\varphi$ in the sense of `FakeEllipticCurve.IsPullback`, the underlying morphism of `pt S' s' E'` is $\operatorname{Spec}\varphi$ followed by that of `pt S s E` (`pt_pullback`); over every algebraically closed field every point of $X$ is of the form `pt k s E` (`pt_surjective`); and `pt k s E = pt k s E'` over an algebraically closed field forces $E$ and $E'$ to be isomorphic (`pt_injective`).
--
--   The geometric fibre over $\bar{\mathbb Q}$. A point $\overline{s} : \operatorname{Spec}\bar{\mathbb Q} \to \operatorname{Spec}\mathbb Z[1/D]$ is given, compatible with the structure maps from $\mathbb Z$ (`sbar_over`). A field $\bar F$ over $\bar{\mathbb Q}$ is given which is a curve over $\bar{\mathbb Q}$ in the project's sense (principal divisors of degree zero exist, residue fields of places are finite over the base, and $\Omega_{\bar F/\bar{\mathbb Q}}$ is free of rank one) and essentially of finite type, a homomorphism `gal` from $\operatorname{Gal}(\bar{\mathbb Q}/\mathbb Q)$ to the group of semilinear automorphisms of $\bar F$ over $\bar{\mathbb Q}$, and a curve model $\mathfrak M$ of $\bar F$ over $\bar{\mathbb Q}$ (an integral scheme $\mathfrak M.C$, proper and smooth of relative dimension $1$ over $\operatorname{Spec}\bar{\mathbb Q}$, with an identification of $\bar F$ with its function field and a bijection between closed points and places matching stalks). Finally $e_{\mathfrak M} : \mathfrak M.C \to X \times_{\operatorname{Spec}\mathbb Z[1/D]} \operatorname{Spec}\bar{\mathbb Q}$ is an isomorphism (`he𝔐`) whose composite with the second projection is $\mathfrak M.\mathrm{toBase}$ (`he𝔐_snd`).
--
--   The uniformised complex curve. A field $F_{c,0}$ over $\mathbb C$ is given, a curve over $\mathbb C$ and essentially of finite type, together with $U_0$, a uniformised Hecke curve for the Fuchsian group $\Gamma = \mathrm{fuchsianGroup}\, R\, \iota$ (the image under $\iota$ of the group generated by the units of $R$, intersected with the kernel of the determinant in $GL_2(\mathbb R)$): thus $U_0$ provides a map $U_0.\mathrm{pt} : \mathfrak H \to \mathrm{Place}(\mathbb C, F_{c,0})$, a realisation $U_0.\mathrm{realize} : F_{c,0} \to \mathfrak H \to \mathbb C$, ramification indices, the characterisations of membership in the valuation ring and of meromorphic order, the criterion $U_0.\mathrm{pt}\,\tau = U_0.\mathrm{pt}\,\tau'$ iff $\tau' \in \Gamma\tau$, Hecke multisets $U_0.\mathrm{heckePoints}\,\ell$ in $GL_2(\mathbb R)$ for primes $\ell$, and a divisor correspondence $\mathrm{corr}$ with $\mathrm{corr}\,\ell$ sending the divisor of $U_0.\mathrm{pt}\,\tau$ to the sum over $\delta$ in $U_0.\mathrm{heckePoints}\,\ell$ of the divisors of $U_0.\mathrm{pt}\,(\delta \cdot \tau)$. The hypothesis `h₀` is a conjunction of nine clauses: (i) $U_0.\mathrm{pt}$ is surjective onto the places of $F_{c,0}$ over $\mathbb C$; (ii) for every prime $\ell$ there is a finite set $S \subseteq \mathbb H[\mathbb Q,a,b]$ such that every $x \in S$ lies in $R$, has reduced norm $\mathrm{nrd}\,x = \ell$, and satisfies $x \otimes 1 = h$ for some $h$ in $\mathrm{levelHeckeUSet}\,\Lambda\,R\,\ell$ if $\ell \mid N$ and in $\mathrm{primeHeckeSet}\,R\,\ell$ otherwise (the local elementary-divisor conditions defining these finite-idelic Hecke sets), such that every $y \in R$ with $\mathrm{nrd}\,y = \ell$ whose $y \otimes 1$ is represented by such an $h$ is $y = u x$ for a unique $x \in S$ with some unit $u$ of $R$ of reduced norm $1$, and such that the multiset $U_0.\mathrm{heckePoints}\,\ell$, viewed in $M_2(\mathbb R)$, equals the multiset of $\iota$-images of the elements of $S$; (iii)–(ix) the analytic clauses: for every $x \in F_{c,0}$ and $\tau \in \mathfrak H$ the function $z \mapsto U_0.\mathrm{realize}\,x$ is meromorphic at $\tau$; near every $\tau$ (eventually in the punctured neighbourhood filter) the realisation is additive, multiplicative, and sends a constant of $\mathbb C$ to that constant; two elements with realisations agreeing near every $\tau$ coincide; realisations are $\Gamma$-invariant near every $\tau$; and every $\Gamma$-invariant function on $\mathfrak H$ which is meromorphic at every $\tau$ agrees, near every $\tau$, with the realisation of some element of $F_{c,0}$.
--
--   The constant field extension. A ring map $\mathrm{emb} : \bar{\mathbb Q} \to \mathbb C$ is given, a field $F_c$ over $\mathbb C$ which is a curve over $\mathbb C$ and essentially of finite type, a ring map $\mathrm{toC} : \bar F \to F_c$, and a map $\mathrm{bcPlace}$ from places of $\bar F$ over $\bar{\mathbb Q}$ to places of $F_c$ over $\mathbb C$. The hypothesis `hcmp` has four clauses: $\mathrm{toC}$ is semilinear over $\mathrm{emb}$ on constants; the subfield of $F_c$ generated by $\mathbb C$ and the image of $\mathrm{toC}$ is everything; $\mathrm{toC}$ carries finite $\bar{\mathbb Q}$-linearly independent families of $\bar F$ to $\mathbb C$-linearly independent families; and for every place $P$ and every $x \in \bar F$, $\mathrm{toC}\,x$ lies in the valuation subring of $\mathrm{bcPlace}\,P$ if and only if $x$ lies in that of $P$. Moreover $\mathrm{bcPlace}$ is injective (`hbc`).
--
--   Conclusion. There exist a period map $\mathrm{per}$ from the places of $\bar F$ over $\bar{\mathbb Q}$ to the upper half-plane $\mathfrak H$ and an isomorphism of $\mathbb C$-algebras $e : F_c \to F_{c,0}$ with the following four properties.
--
--   First, for every place $P$ of $\bar F$ over $\bar{\mathbb Q}$ and every $x \in F_c$: $e\,x$ lies in the valuation subring of $U_0.\mathrm{pt}(\mathrm{per}\,P)$ if and only if $x$ lies in the valuation subring of $\mathrm{bcPlace}\,P$.
--
--   Second, for every prime $\ell$ with $\ell \neq q$ and $\ell \neq q'$, every place $P$ and every fake elliptic curve $E$ over $\bar{\mathbb Q}$ of type `FakeEllipticCurve Λ N (AlgebraicClosure ℚ)` whose moduli point satisfies $(\mathrm{pt}\,\bar{\mathbb Q}\,\overline{s}\,E).1 = (\mathfrak M.\mathrm{pointEquivPlace}^{-1} P).1$ followed by $e_{\mathfrak M}$ followed by the first projection of the pullback, there exist $n \in \mathbb N$, a family $K : \mathrm{Fin}\,n \to E.\mathrm{ExtraLevel}\,\ell$ of full level-$\ell$ subgroup data on $E$ (each given by a closed immersion $\mathrm{levK}$ whose points form an $\ell$-torsion subgroup stable under $\Lambda$, disjoint from the level datum, finite flat of rank $\ell^2$, and isomorphic to $\mathbb Z/\ell \times \mathbb Z/\ell$ on geometric fibres), a family $d : \mathrm{Fin}\,n \to \mathrm{FakeEllipticCurve}\,\Lambda\,N\,\bar{\mathbb Q}$ and a family $P_\bullet : \mathrm{Fin}\,n \to \mathrm{Place}(\bar{\mathbb Q}, \bar F)$ such that: the $K i$ are pairwise distinguished by their $\bar{\mathbb Q}$-points, in the sense that if $\mathrm{FactorsThrough}\,(K i).\mathrm{levK}$ and $\mathrm{FactorsThrough}\,(K j).\mathrm{levK}$ hold for the same points over the identity of $\operatorname{Spec}\bar{\mathbb Q}$ then $i = j$; every level-$\ell$ datum $K'$ on $E$ has the same such points as some $K i$; for each $i$ the curve $d i$ is a level-$\ell$ isogeny quotient of the pair $\langle E, K i\rangle$, that is $\mathrm{IsLevelIsogeny}\,\ell\,\langle E, K i\rangle\,(d i)$ holds (a $\Lambda$-equivariant pair of homomorphisms whose composites are the action of $\ell$, with kernel exactly $(K i).\mathrm{levK}$ and preserving the level data); for each $i$ the moduli point of $d i$ is the point attached to $P_\bullet i$ by the same formula as for $P$; and the multiset obtained from $U_0.\mathrm{heckePoints}\,\ell$ by $\delta \mapsto U_0.\mathrm{pt}(\delta \cdot \mathrm{per}\,P)$ equals the multiset of $U_0.\mathrm{pt}(\mathrm{per}(P_\bullet i))$ for $i$ running over $\mathrm{Fin}\,n$.
--
--   Third, for all places $P, Q$ and all fake elliptic curves $E, E'$ over $\bar{\mathbb Q}$ whose moduli points are those attached to $P$ and to $Q$ respectively (by the formula above), if $E'$ is an Atkin–Lehner quotient of $E$ at $q$, in the sense that $\mathrm{IsAtkinLehnerQuotient}\,q\,E\,E'$ holds ($\Lambda$-equivariant homomorphisms both ways whose composites are the action of $q$, with kernel characterised by annihilation under all $m \in \Lambda$ with $m m^{*}$ an integral multiple of $q$, and preserving the level data), then the multiset obtained from $U_0.\mathrm{heckePoints}\,q$ by $\delta \mapsto U_0.\mathrm{pt}(\delta \cdot \mathrm{per}\,P)$ is the singleton $\{U_0.\mathrm{pt}(\mathrm{per}\,Q)\}$.
--
--   Fourth, the same assertion with $q'$ in place of $q$ throughout.
--
--   This is Shimura's complex uniformisation of the coarse moduli curve of fake elliptic curves with $\Lambda$-action and level-$N$ structure, stated in period form: it produces the period map from places of the geometric function field to the upper half-plane together with an identification of the complexified function field with the field of $\Gamma$-invariant meromorphic functions, and it translates level-$\ell$ isogeny quotients and the Atkin–Lehner involutions at $q$ and $q'$ into the Hecke translates of periods. It feeds [`CerednikDrinfeld.QM.exists_uniformizedHeckeCurve_bcPlace_corr_single_eq_sum_of_two_mul_dvd`](thm.html#CerednikDrinfeld.QM.exists_uniformizedHeckeCurve_bcPlace_corr_single_eq_sum_of_two_mul_dvd), where the dictionary is recast as an identity of divisors under the Hecke correspondence.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_period_algEquiv_pt_iff_bcPlace_of_uniformizedHeckeCurve_of_two_mul_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology

theorem CerednikDrinfeld.QM.exists_period_algEquiv_pt_iff_bcPlace_of_uniformizedHeckeCurve_of_two_mul_dvd
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) (hD : 2 * N * q * q' ∣ D)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)

    (X : Scheme.{0}) [hXint : IsIntegral X]
    (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (hsmooth : Smooth πX) (hproper : IsProper πX)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ _) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ _) (s' : Spec (CommRingCat.of S') ⟶ _),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _) (P : SchemeHomOver s πX),
      ∃ E : FakeEllipticCurve Λ N k, pt k s E = P)
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _)
      (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')
    (hsmooth1 : SmoothOfRelativeDimension 1 πX)
    (hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      IsIntegral (CategoryTheory.Limits.pullback πX s))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (sbar_over : sbar ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away ((D : ℕ) : ℤ)))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))

    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) (he𝔐 : IsIso e𝔐)
    (he𝔐_snd : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)

    (Fc₀ : Type) [Field Fc₀] [Algebra ℂ Fc₀] [AlgebraicCurve.IsCurveOver ℂ Fc₀] [Algebra.EssFiniteType ℂ Fc₀]
    (U₀ : ModularCurve.UniformizedHeckeCurve (fuchsianGroup R ι) Fc₀)
    (h₀ :
      Function.Surjective U₀.pt ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ∃ S : Finset ℍ[ℚ, a, b],
        (∀ x ∈ S, x ∈ R ∧ nrd x = ℓ ∧
          ∃ h ∈ (if ℓ ∣ N then levelHeckeUSet Λ R ℓ else primeHeckeSet R ℓ),
            (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = x ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) ∧
        (∀ y : ℍ[ℚ, a, b], y ∈ R → nrd y = ℓ →
          (∃ h ∈ (if ℓ ∣ N then levelHeckeUSet Λ R ℓ else primeHeckeSet R ℓ),
            (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = y ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) →
          ∃! x, x ∈ S ∧ ∃ u : ℍ[ℚ, a, b], IsUnitOf R u ∧ nrd u = 1 ∧ u * x = y) ∧
        (U₀.heckePoints ℓ hℓ).map (fun g => (g : Matrix (Fin 2) (Fin 2) ℝ)) = S.val.map ι) ∧
      (∀ (x : Fc₀) (τ : UpperHalfPlane), MeromorphicAt (fun z : ℂ => U₀.realize x (UpperHalfPlane.ofComplex z)) (τ : ℂ)) ∧
      (∀ (x y : Fc₀) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, U₀.realize (x + y) z = U₀.realize x z + U₀.realize y z) ∧
      (∀ (x y : Fc₀) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, U₀.realize (x * y) z = U₀.realize x z * U₀.realize y z) ∧
      (∀ (c : ℂ) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, U₀.realize (algebraMap ℂ Fc₀ c) z = c) ∧
      (∀ x y : Fc₀, (∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, U₀.realize x z = U₀.realize y z) → x = y) ∧
      (∀ x : Fc₀, ∀ γ ∈ fuchsianGroup R ι, ∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, U₀.realize x (γ • z) = U₀.realize x z) ∧
      (∀ f : UpperHalfPlane → ℂ, (∀ τ : UpperHalfPlane, MeromorphicAt (fun z : ℂ => f (UpperHalfPlane.ofComplex z)) (τ : ℂ)) →
        (∀ γ ∈ fuchsianGroup R ι, ∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, f (γ • z) = f z) →
        ∃ x : Fc₀, ∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, U₀.realize x z = f z))

    (emb : AlgebraicClosure ℚ →+* ℂ)
    (Fc : Type) [Field Fc] [Algebra ℂ Fc] [AlgebraicCurve.IsCurveOver ℂ Fc] [Algebra.EssFiniteType ℂ Fc]
    (toC : Fbar →+* Fc) (bcPlace : Place (AlgebraicClosure ℚ) Fbar → Place ℂ Fc)
    (hcmp :
      (∀ z : AlgebraicClosure ℚ, toC (algebraMap (AlgebraicClosure ℚ) Fbar z) = algebraMap ℂ Fc (emb z)) ∧
      Subfield.closure (Set.range (algebraMap ℂ Fc) ∪ Set.range toC) = ⊤ ∧
      (∀ s : Finset Fbar, LinearIndependent (AlgebraicClosure ℚ) (fun x : s => (x : Fbar)) →
        LinearIndependent ℂ (fun x : s => toC (x : Fbar))) ∧
      (∀ (P : Place (AlgebraicClosure ℚ) Fbar) (x : Fbar), toC x ∈ (bcPlace P).toValuationSubring ↔ x ∈ P.toValuationSubring))
    (hbc : Function.Injective bcPlace) :
    ∃ (per : Place (AlgebraicClosure ℚ) Fbar → UpperHalfPlane) (e : Fc ≃ₐ[ℂ] Fc₀),

      (∀ (P : Place (AlgebraicClosure ℚ) Fbar) (x : Fc),
        e x ∈ (U₀.pt (per P)).toValuationSubring ↔ x ∈ (bcPlace P).toValuationSubring) ∧

      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ≠ q → ℓ ≠ q' →
        ∀ (P : Place (AlgebraicClosure ℚ) Fbar) (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)),
          (pt _ sbar E).1 = (𝔐.pointEquivPlace.symm P).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar →
          ∃ (n : ℕ) (K : Fin n → E.ExtraLevel ℓ) (d : Fin n → FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
            (Ps : Fin n → Place (AlgebraicClosure ℚ) Fbar),
            (∀ i j : Fin n,
                (∀ x : SchemeHomOver (CategoryTheory.CategoryStruct.id (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f,
                  FactorsThrough (K i).levK x ↔ FactorsThrough (K j).levK x) → i = j) ∧
            (∀ K' : E.ExtraLevel ℓ, ∃ i : Fin n,
                ∀ x : SchemeHomOver (CategoryTheory.CategoryStruct.id (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f,
                  FactorsThrough K'.levK x ↔ FactorsThrough (K i).levK x) ∧
            (∀ i : Fin n, FakeEllipticCurve.IsLevelIsogeny ℓ
                (⟨E, K i⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ)) (d i)) ∧
            (∀ i : Fin n, (pt _ sbar (d i)).1 = (𝔐.pointEquivPlace.symm (Ps i)).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar) ∧
            ((U₀.heckePoints ℓ hℓ).map (fun δ => U₀.pt (δ • per P))) =
              (Finset.univ.val.map (fun i : Fin n => U₀.pt (per (Ps i))))) ∧

      (∀ (P Q : Place (AlgebraicClosure ℚ) Fbar) (E E' : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)),
        (pt _ sbar E).1 = (𝔐.pointEquivPlace.symm P).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar →
        (pt _ sbar E').1 = (𝔐.pointEquivPlace.symm Q).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar →
        E.IsAtkinLehnerQuotient q E' →
        ((U₀.heckePoints q Fact.out).map (fun δ => U₀.pt (δ • per P))) = {U₀.pt (per Q)}) ∧
      (∀ (P Q : Place (AlgebraicClosure ℚ) Fbar) (E E' : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)),
        (pt _ sbar E).1 = (𝔐.pointEquivPlace.symm P).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar →
        (pt _ sbar E').1 = (𝔐.pointEquivPlace.symm Q).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar →
        E.IsAtkinLehnerQuotient q' E' →
        ((U₀.heckePoints q' Fact.out).map (fun δ => U₀.pt (δ • per P))) = {U₀.pt (per Q)}) := by sorry
