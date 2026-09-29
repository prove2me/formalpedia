-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isFineModuli_quasiProjective_of_trunk
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isFineModuli_quasiProjective_of_trunk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/7a8c2e11-0bcb-588b-a629-b095df9009f7
-- title:
--   Quasi-projective fine moduli of framed polarised abelian schemes
-- statement:
--   Fix natural numbers $g$, $N$, $n$ and a commutative ring $\mathcal O$ (of type `Type`, i.e. in universe $0$) in which the image of $n$ is a unit (`hn'`).
--
--   Here a `FramedPolarisedAbelianScheme g N n S` over a commutative ring $S$ consists of a `PolarisedAbelianScheme g (N+1) n S` — a scheme $A$ with $f : A \to \operatorname{Spec} S$, a commutative relative group law $L$ on $f$ (a functorial group structure on $T$-points over $\operatorname{Spec} S$), an `AbelianSchemePropertyBundle` for $f$ (smooth, proper, connected fibres, and a relative group law exists), all fibres of topological Krull dimension $g$, sections $P_0,\dots,P_{2g-1}$ of $f$ killed by $n$ which on every geometric fibre over an algebraically closed field freely parametrise the $n$-torsion via $c \mapsto \sum c_i P_i$ (injectively, and surjectively onto the $n$-torsion points), and an invertible module $\mathrm{pol}$ on $A$ admitting a closed immersion by sections and with geometric fibrewise $H^0$-rank equal to $N+1$ — together with a frame: a `ProjPresentation` of $\mathrm{pol}$ over $f$ with $N+1$ global sections, whose associated morphism `frame.toProj` to $\operatorname{Proj}$ of the graded ring of homogeneous polynomials in $N+1$ variables over $S$ is a closed immersion, and whose sections form a section basis, meaning that $c \mapsto \sum_i f^\#(c_i)\,\sigma_i$ is a bijection from $(\mathrm{Fin}\,(N+1) \to S)$ onto the global sections of $\mathrm{pol}$.
--
--   The statement is in hypothesis form: ten families of inputs are assumed, each stated for arbitrary base rings and schemes. Their bound variables $g$, $N$, $n$, $P$ and so on are local to each hypothesis and unrelated to the outer $g$, $N$, $n$.
--
--   `hH1B` (Hilbert scheme bridge): for every $n$ and every $P \in \mathbb Q[t]$ which is realised as the eventual Hilbert polynomial of some homogeneous ideal $I$ in a polynomial ring in $n+1$ variables over some field $K$ (the ideal is closed under taking homogeneous components, and $\dim_K (\text{degree-}d\text{ piece of } K[x]/I) = P(d)$ for all large $d$), there is $D_0$ such that for every $m \ge D_0$ there exist a scheme $\mathrm{Hilb}$ (in universe $0$), a morphism $p : \mathrm{Hilb} \to \operatorname{Spec} \mathbb Z$ and, for every commutative ring $A$, a bijection $\mathrm{pt}_A$ between the `Point`s of type $(n, \mathrm{hilbertFunctionOf}\ n\ P\ m)$ over $A$ — homogeneous ideals of $A[x_0,\dots,x_n]$ all of whose graded quotient pieces are finite projective of rank $\mathrm{hilbertFunctionOf}\ n\ P\ m(d)$ at every prime, this function being $d \mapsto \binom{n+d}{n}$ for $d < m$ and $d \mapsto \lfloor P(d)\rfloor$ otherwise — and morphisms $\operatorname{Spec} A \to \mathrm{Hilb}$, subject to: for every ring map $\varphi : A \to B$ and every point $x$ over $A$ there is a point $y$ over $B$ with $y.I = (\mathrm{map}\ \varphi)(x.I)$; the relation $y.I = (\mathrm{map}\ \varphi)(x.I)$ holds precisely when $\mathrm{pt}_B\,y$ equals $\operatorname{Spec}\varphi$ followed by $\mathrm{pt}_A\,x$; each $\mathrm{pt}_A\,x$ followed by $p$ is $\operatorname{Spec}$ of the structure map $\mathbb Z \to A$; $p$ is proper and locally of finite presentation; every finite set of points of $\mathrm{Hilb}$ lies in one affine open; and there are $N$ and a closed immersion $\iota$ of $\mathrm{Hilb}$ into $\operatorname{Proj}$ of the homogeneous polynomials in $N+1$ variables over $\mathbb Z$ with $\iota$ followed by the projection to $\operatorname{Spec}\mathbb Z$ equal to $p$.
--
--   `hCBC` (cohomology and base change for the polarisation): for every ring $S$, every $f : A \to \operatorname{Spec} S$ carrying a relative group law $L$ and an `AbelianSchemePropertyBundle`, and every invertible module $\mathcal L$ on $A$ admitting a closed immersion by sections over $f$, four conclusions hold: the $S$-module of global sections of $\mathcal L$ (with the module structure induced by $f$ on global sections) is finite and projective; for each point $s$ of $\operatorname{Spec} S$ there is $r \notin s$ such that after any localisation away from $r$ and any base change of $f$ along it, the pulled-back module admits finitely many sections forming a section basis on the preimage of the whole space; any section basis $\sigma$ of $\mathcal L$ pulls back, along any base change $\varphi : S \to S'$ realised by a pullback square, to a section basis of the pulled-back module; and if $\sigma$ is a section basis of length $m$ then `geomFibreH0Finrank` of $f$ and $\mathcal L$ at every algebraically closed field $k$ and every $S \to k$ equals $m$.
--
--   `hH2a` (openness of the smooth locus): for $f : Z \to \operatorname{Spec} S$ proper, flat and locally of finite presentation and for each $g$, the set of points $s$ of $\operatorname{Spec} S$ such that every geometric fibre at $s$ (pullback along $\operatorname{Spec} k \to \operatorname{Spec} S$ given by a map $S \to k$ with $k$ algebraically closed and kernel $s$) is smooth, irreducible and of topological Krull dimension $g$, is open; and the restriction of $f$ over any open $V$ contained in that set is smooth.
--
--   `hH2b` (existence and uniqueness of the group law): for a Noetherian ring $R$ and $f : A \to \operatorname{Spec} R$ which is smooth, proper, with connected fibres, equipped with $N$ and a closed immersion $\iota$ into $\operatorname{Proj}$ over $R$ satisfying $\iota$ followed by the projection $= f$, a section $e$ of $f$, and the hypothesis that every geometric fibre of $f$ satisfies `AbelianSchemePropertyBundle`, there is a relative group law $L$ on $f$ whose unit section is $e$, which is commutative, and which is the unique relative group law with unit $e$.
--
--   `hH2bp` (openness of the abelian locus): for $f : Z \to \operatorname{Spec} S$ smooth and proper, admitting $N$ and a closed immersion into $\operatorname{Proj}$ over $S$ compatible with $f$, with all geometric fibres connected, and given a section $\varepsilon$ of $f$, the set of $s \in \operatorname{Spec} S$ all of whose geometric fibres admit a relative group law is open.
--
--   `hTORS` (torsion locus is cut out by an ideal): for a relative group law $L$ on $f : A \to \operatorname{Spec} S$ with an `AbelianSchemePropertyBundle`, for $n$ and a section $P$ of $f$, there is an ideal $I \subseteq S$ such that for every $\varphi : S \to S'$ the base change of $P$ along $\varphi$ is killed by $n$ precisely when $I \subseteq \ker \varphi$.
--
--   `hLEVEL` (clopenness of the full level-$n$ locus): for a commutative relative group law $L$ on $f$ with an `AbelianSchemePropertyBundle`, all fibres of topological Krull dimension $g$, $n$ a unit in $S$, and sections $P_0,\dots,P_{2g-1}$ of $f$ each killed by $n$, the set of $s \in \operatorname{Spec} S$ such that on every geometric fibre at $s$ the map $c \mapsto \sum_i c_i P_i$ from $(\mathrm{Fin}\,(2g) \to \mathrm{Fin}\,n)$ is injective and hits every $n$-torsion point, is clopen.
--
--   `hLINSYS` (the section-basis locus is open): for $L$, an `AbelianSchemePropertyBundle`, an invertible $\mathcal L$ admitting a closed immersion by sections, and sections $\tau_0,\dots,\tau_{m-1}$ of $\mathcal L$, there is an open $U \subseteq \operatorname{Spec} S$ such that for every $\varphi : S \to S'$ and every pullback square over $\operatorname{Spec}\varphi$, the pulled-back $\tau_i$ form a section basis exactly when the image of the induced map on prime spectra lies in $U$.
--
--   `hFBC` (base change of framed objects): for every $\varphi : S \to S'$ and every framed polarised abelian scheme $X$ of type $(g,N,n)$ over $S$ there is such an object $X'$ over $S'$ with `FramedPolarisedAbelianScheme.IsPullback` $\varphi$ $X$ $X'$.
--
--   `hD2` (section bases give closed immersions): if $\mathcal L$ admits a closed immersion by sections over $f$, and $\mathfrak P$ is a `ProjPresentation` of $\mathcal L$ over $f$ whose sections form a section basis, then $\mathfrak P.\mathrm{toProj}$ is a closed immersion.
--
--   Under these hypotheses the conclusion asserts the existence of a scheme $H$ in universe $0$, a morphism $\pi_H : H \to \operatorname{Spec}\mathcal O$, and an assignment $\mathrm{pt}_H$ sending each commutative ring $S$, each morphism $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal O$ and each framed polarised abelian scheme of type $(g,N,n)$ over $S$ to a morphism $\operatorname{Spec} S \to H$ whose composite with $\pi_H$ is $s$, such that the following hold.
--
--   First, `FramedPolarisedAbelianScheme.IsFineModuli g N n H πH ptH`: isomorphic framed objects over the same $S$ and $s$ have equal associated points; for $\varphi : S \to S'$ and $s$, $s'$ with $\operatorname{Spec}\varphi$ followed by $s$ equal to $s'$, if $X'$ is a pullback of $X$ along $\varphi$ then the morphism attached to $X'$ is $\operatorname{Spec}\varphi$ followed by the morphism attached to $X$; every morphism $\operatorname{Spec} S \to H$ over $s$ arises as $\mathrm{pt}_H$ of some framed object over $S$; and two framed objects over $S$ with the same associated point are related by the isomorphism relation `Iso`.
--
--   Second, $\pi_H$ is separated, quasi-compact and locally of finite presentation. Third, every finite set of points of $H$ is contained in a single affine open of $H$. Fourth, there exist $\mathrm{qpn} \in \mathbb N$ and a morphism $\mathrm{qp}\iota$ from $H$ to $\operatorname{Proj}$ of the graded ring of homogeneous polynomials in $\mathrm{qpn}+1$ variables over $\mathcal O$ which is an immersion and satisfies $\mathrm{qp}\iota$ followed by `ProjSpace.π 𝒪 qpn` $= \pi_H$; thus $\pi_H$ is quasi-projective in this explicit sense.
--
--   This is the assembly step in the construction of the rigidified (framed) moduli scheme of polarised abelian schemes with full level-$n$ structure over a base ring $\mathcal O$ in which $n$ is invertible: granted the Hilbert-scheme representability input, cohomology and base change for the polarisation, openness of the smooth and of the abelian locus, the torsion and level-structure loci, the section-basis criterion and base change of framed objects, the universal framed family is cut out inside a Hilbert scheme of projective space and shown to represent the framed moduli problem, with separated, quasi-compact, locally finitely presented and quasi-projective structure morphism. It is used by [`AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isFineModuli_quasiProjective`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isFineModuli_quasiProjective), where the hypotheses are discharged, and sits on the route to good-reduction and Néron-model properties of Jacobians needed later.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isFineModuli_quasiProjective_of_trunk.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPolynomial CategoryTheory AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isFineModuli_quasiProjective_of_trunk
    (g N n : ℕ) (𝒪 : Type) [CommRing 𝒪] (hn' : IsUnit ((n : ℕ) : 𝒪))
    (hH1B : ∀ (n : ℕ) (P : Polynomial ℚ)
      (hP : ∃ (K : Type) (_ : Field K) (I : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
      ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) = P.eval (d : ℚ)),
      ∃ D₀ : ℕ, ∀ m : ℕ, D₀ ≤ m →
      ∃ (Hilb : Scheme.{0}) (p : Hilb ⟶ Spec (CommRingCat.of ℤ))
      (pt : ∀ (A : Type) [CommRing A],
      Point A n (hilbertFunctionOf n P m) ≃ (Spec (CommRingCat.of A) ⟶ Hilb)),
      (∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B)
      (x : Point A n (hilbertFunctionOf n P m)),
      ∃ y : Point B n (hilbertFunctionOf n P m), y.I = Ideal.map (MvPolynomial.map φ) x.I) ∧
      (∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B)
      (x : Point A n (hilbertFunctionOf n P m)) (y : Point B n (hilbertFunctionOf n P m)),
      y.I = Ideal.map (MvPolynomial.map φ) x.I ↔
      pt B y = Spec.map (CommRingCat.ofHom φ) ≫ pt A x) ∧
      (∀ (A : Type) [CommRing A] (x : Point A n (hilbertFunctionOf n P m)),
      pt A x ≫ p = Spec.map (CommRingCat.ofHom (algebraMap ℤ A))) ∧
      IsProper p ∧ LocallyOfFinitePresentation p ∧
      (∀ F : Finset Hilb, ∃ U : Hilb.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) ∧
      ∃ (N : ℕ) (ι : Hilb ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℤ)),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π ℤ N = p)
    (hCBC : ∀ {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
      (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
      (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) (hva : Scheme.Modules.ClosedImmersionBySections 𝓛 f),
      (letI : Module S Γ(𝓛, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom
      Module.Finite S Γ(𝓛, ⊤) ∧ Module.Projective S Γ(𝓛, ⊤)) ∧
      (∀ s : ↥(Spec (CommRingCat.of S)), ∃ r : S, r ∉ s.asIdeal ∧
      ∀ (S' : Type) [CommRing S'] [Algebra S S'] [IsLocalization.Away r S']
      (A' : Scheme) (f' : A' ⟶ Spec (CommRingCat.of S')) (gA : A' ⟶ A),
      CategoryTheory.IsPullback gA f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) →
      ∃ (m : ℕ) (σ' : Fin m → Γ((Scheme.Modules.pullback gA).obj 𝓛, gA ⁻¹ᵁ ⊤)),
      Scheme.Modules.IsSectionBasisOn f' ((Scheme.Modules.pullback gA).obj 𝓛) (gA ⁻¹ᵁ ⊤) σ') ∧
      (∀ {m : ℕ} (σ : Fin m → Γ(𝓛, ⊤)), Scheme.Modules.IsSectionBasis f 𝓛 σ →
      ∀ (S' : Type) [CommRing S'] (φ : S →+* S')
      (A' : Scheme) (f' : A' ⟶ Spec (CommRingCat.of S')) (gA : A' ⟶ A),
      CategoryTheory.IsPullback gA f' f (Spec.map (CommRingCat.ofHom φ)) →
      Scheme.Modules.IsSectionBasisOn f' ((Scheme.Modules.pullback gA).obj 𝓛) (gA ⁻¹ᵁ ⊤)
      (fun i => Scheme.Modules.pullbackLocalSection gA (σ i))) ∧
      (∀ {m : ℕ} (σ : Fin m → Γ(𝓛, ⊤)), Scheme.Modules.IsSectionBasis f 𝓛 σ →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k), Scheme.Modules.geomFibreH0Finrank f 𝓛 k sk = m))
    (hH2a : ∀ {S : Type} [CommRing S] {Z : Scheme} (f : Z ⟶ Spec (CommRingCat.of S))
      [IsProper f] [Flat f] [LocallyOfFinitePresentation f] (g : ℕ),
      IsOpen {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type) [Field k] [IsAlgClosed k] (x : S →+* k),
      RingHom.ker x = s.asIdeal →
      Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x))) ∧
      IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))) ∧
      topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x))) = g} ∧
      ∀ V : (Spec (CommRingCat.of S)).Opens,
      (V : Set ↥(Spec (CommRingCat.of S))) ⊆ {s | ∀ (k : Type) [Field k] [IsAlgClosed k] (x : S →+* k),
      RingHom.ker x = s.asIdeal →
      Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x))) ∧
      IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))) ∧
      topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x))) = g} →
      Smooth (f ∣_ V))
    (hH2b : ∀ {R : Type} [CommRing R] [IsNoetherianRing R] {A : Scheme} (f : A ⟶ Spec (CommRingCat.of R))
      (hs : Smooth f) (hp : IsProper f) (hc : ∀ s : Spec (CommRingCat.of R), _root_.IsConnected (f.base ⁻¹' {s}))
      (N : ℕ) (ι : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (hι : IsClosedImmersion ι)
      (hιf : ι ≫ ProjSpace.π R N = f)
      (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
      (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      AbelianSchemePropertyBundle k (pullback.snd f s)),
      ∃ L : RelativeGroupLaw R f, L.one (𝟙 _) = e ∧ L.IsCommutative ∧
      ∀ L' : RelativeGroupLaw R f, L'.one (𝟙 _) = e → L' = L)
    (hH2bp : ∀ {S : Type} [CommRing S] {Z : Scheme} (f : Z ⟶ Spec (CommRingCat.of S))
      (hsm : Smooth f) (hpr : IsProper f)
      (hproj : ∃ (N : ℕ) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π S N = f)
      (hconn : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : S →+* k),
      ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))))
      (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f),
      IsOpen {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type) [Field k] [IsAlgClosed k] (x : S →+* k),
      RingHom.ker x = s.asIdeal →
      Nonempty (RelativeGroupLaw k (pullback.snd f (Spec.map (CommRingCat.ofHom x))))})
    (hTORS : ∀ {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
      (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f) (n : ℕ)
      (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f),
      ∃ I : Ideal S, ∀ (S' : Type) [CommRing S'] (φ : S →+* S'),
      L.nsmul (Spec.map (CommRingCat.ofHom φ)) n
      (schemeHomOverComp (Spec.map (CommRingCat.ofHom φ)) (Category.comp_id _) P) =
      L.one (Spec.map (CommRingCat.ofHom φ)) ↔ I ≤ RingHom.ker φ)
    (hLEVEL : ∀ {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
      (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
      (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of S)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
      (n : ℕ) (hn : IsUnit ((n : ℕ) : S))
      (P : Fin (2 * g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
      (hP : ∀ i, L.nsmul (𝟙 (Spec (CommRingCat.of S))) n (P i) = L.one (𝟙 (Spec (CommRingCat.of S)))),
      IsClopen {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k),
      RingHom.ker sk = s.asIdeal →
      (∀ c c' : Fin (2 * g) → Fin n,
      L.finComb (Spec.map (CommRingCat.ofHom sk))
      (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c i : ℕ)) =
      L.finComb (Spec.map (CommRingCat.ofHom sk))
      (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c' i : ℕ)) →
      c = c') ∧
      (∀ Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f,
      L.nsmul (Spec.map (CommRingCat.ofHom sk)) n Q = L.one (Spec.map (CommRingCat.ofHom sk)) →
      ∃ c : Fin (2 * g) → Fin n,
      L.finComb (Spec.map (CommRingCat.ofHom sk))
      (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c i : ℕ)) = Q)})
    (hLINSYS : ∀ {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
      (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
      (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) (hva : Scheme.Modules.ClosedImmersionBySections 𝓛 f)
      {m : ℕ} (τ : Fin m → Γ(𝓛, ⊤)),
      ∃ U : Set ↥(Spec (CommRingCat.of S)), IsOpen U ∧
      ∀ (S' : Type) [CommRing S'] (φ : S →+* S')
      (A' : Scheme) (f' : A' ⟶ Spec (CommRingCat.of S')) (gA : A' ⟶ A),
      CategoryTheory.IsPullback gA f' f (Spec.map (CommRingCat.ofHom φ)) →
      (Scheme.Modules.IsSectionBasisOn f' ((Scheme.Modules.pullback gA).obj 𝓛) (gA ⁻¹ᵁ ⊤)
      (fun i => Scheme.Modules.pullbackLocalSection gA (τ i)) ↔
      Set.range (PrimeSpectrum.comap φ) ⊆ U))
    (hFBC : ∀ {g N n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
      (X : FramedPolarisedAbelianScheme g N n S),
      ∃ X' : FramedPolarisedAbelianScheme g N n S', FramedPolarisedAbelianScheme.IsPullback φ X X')
    (hD2 : ∀ {S : Type} [CommRing S] {X : Scheme} {f : X ⟶ Spec (CommRingCat.of S)} {𝓛 : X.Modules}
      (hva : Scheme.Modules.ClosedImmersionBySections 𝓛 f)
      {N : ℕ} (𝔓 : Scheme.Modules.ProjPresentation 𝓛 f N) (hσ : Scheme.Modules.IsSectionBasis f 𝓛 𝔓.σ),
      IsClosedImmersion 𝔓.toProj) :
    ∃ (H : Scheme.{0}) (πH : H ⟶ Spec (CommRingCat.of 𝒪))
      (ptH : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
        FramedPolarisedAbelianScheme g N n S → SchemeHomOver s πH),
      FramedPolarisedAbelianScheme.IsFineModuli g N n H πH ptH ∧
      IsSeparated πH ∧ QuasiCompact πH ∧ LocallyOfFinitePresentation πH ∧
      (∀ F : Finset H, ∃ U : H.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) ∧
      (∃ (qpn : ℕ) (qpι : H ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) 𝒪)),
        IsImmersion qpι ∧ qpι ≫ ProjSpace.π 𝒪 qpn = πH) := by sorry
