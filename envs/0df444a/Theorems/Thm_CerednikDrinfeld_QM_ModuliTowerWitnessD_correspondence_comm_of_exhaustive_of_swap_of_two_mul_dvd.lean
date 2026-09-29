-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_correspondence_comm_of_exhaustive_of_swap_of_two_mul_dvd
-- name    : CerednikDrinfeld.QM.ModuliTowerWitnessD.correspondence_comm_of_exhaustive_of_swap_of_two_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/39ec6777-2e4d-50d8-a6d3-c45159809731
-- title:
--   Hecke correspondences at two primes away from qq' commute
-- statement:
--   Fix a nonzero natural number $N$ and primes $q,q'$ with $q'\neq q$, with $q\nmid N$ and $q'\nmid N$, and a natural number $D$ divisible by $2Nqq'$. Fix rationals $a,b$ for which `IsIndefiniteRamifiedExactlyAt a b q q'` holds, that is: $a>0$ or $b>0$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit if and only if $v$ contains $q$ or $q'$. Fix a $\mathbb{Z}$-submodule $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ which is a maximal order in the sense of `IsMaximalOrder`: $\Lambda$ contains $1$, is closed under multiplication, spans $\mathbb{H}[\mathbb{Q},a,b]$ over $\mathbb{Q}$, is finitely generated, and every order containing $\Lambda$ equals $\Lambda$.
--
--   The coarse moduli package over $\mathbb{Z}[1/D]$ consists of: an integral scheme $X$ with a morphism $\pi_X\colon X\to\operatorname{Spec}\mathbb{Z}[1/D]$ (the base being $\operatorname{Spec}$ of the localisation of $\mathbb{Z}$ away from $D$), which is assumed smooth (`hsmooth`), proper (`hproper`) and smooth of relative dimension $1$ (`hsmooth1`), and whose base changes along points of the base with algebraically closed residue field are integral (`hgeom`); and an assignment `pt` sending each commutative ring $S$, each morphism $s\colon\operatorname{Spec}S\to\operatorname{Spec}\mathbb{Z}[1/D]$ and each fake elliptic curve $E$ for $(\Lambda,N)$ over $S$ to a point of $X$ over $s$, i.e. a morphism $\operatorname{Spec}S\to X$ whose composite with $\pi_X$ is $s$. The assignment is assumed to satisfy: invariance under isomorphism of fake elliptic curves (`pt_iso`); compatibility with base change (`pt_pullback`), namely for a ring homomorphism $\varphi\colon S\to S'$ and base points $s,s'$ with $\operatorname{Spec}\varphi$ followed by $s$ equal to $s'$, and for $E$ over $S$ and $E'$ over $S'$ with $E'$ a pullback of $E$ along $\varphi$ in the sense of `FakeEllipticCurve.IsPullback`, the point of $E'$ is $\operatorname{Spec}\varphi$ followed by the point of $E$; surjectivity on points with values in algebraically closed fields (`pt_surjective`); and injectivity up to isomorphism on such points (`pt_injective`).
--
--   The geometric fibre data consist of: a morphism $\bar s\colon\operatorname{Spec}\overline{\mathbb{Q}}\to\operatorname{Spec}\mathbb{Z}[1/D]$ whose composite with the structure morphism to $\operatorname{Spec}\mathbb{Z}$ is the one induced by $\mathbb{Z}\to\overline{\mathbb{Q}}$ (`sbar_over`); a field $\bar F$ which is an essentially finite type $\overline{\mathbb{Q}}$-algebra and a curve over $\overline{\mathbb{Q}}$ in the sense of `IsCurveOver` (principal divisors exist, each place has residue field finite over $\overline{\mathbb{Q}}$, and $\Omega_{\bar F/\overline{\mathbb{Q}}}$ is free of rank one); a homomorphism `gal` from $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to the group of semilinear automorphisms of $\bar F$ over $\overline{\mathbb{Q}}$ (pairs of ring automorphisms of $\bar F$ and of $\overline{\mathbb{Q}}$ compatible with the structure map); a curve model $\mathfrak{M}$ of $\bar F$ over $\overline{\mathbb{Q}}$ (an integral scheme, proper and smooth of relative dimension $1$ over $\overline{\mathbb{Q}}$, with function field identified with $\bar F$ and closed points in bijection with the places of $\bar F$); and a morphism $e_{\mathfrak{M}}\colon\mathfrak{M}.C\to X\times_{\operatorname{Spec}\mathbb{Z}[1/D]}\operatorname{Spec}\overline{\mathbb{Q}}$ which is an isomorphism (`he𝔐`) and whose composite with the second projection is the structure morphism $\mathfrak{M}.\mathrm{toBase}$ (`he𝔐_snd`).
--
--   The tower data consist of: $\mathbb{T}$ of type `HeckeTower.TowerData q q' Fbar`, assigning to each prime $\ell\notin\{q,q'\}$ a field $\mathbb{T}.F\,\ell$ which is a curve over $\overline{\mathbb{Q}}$ of essentially finite type, and to each pair $(\ell,i)$ with $i\in\{0,1\}$ an $\overline{\mathbb{Q}}$-algebra map $\mathbb{T}.\varphi\,(\ell,i)\colon\bar F\to\mathbb{T}.F\,\ell$ which is finite and integral (the integrality witnesses being $\mathbb{T}.\mathrm{integral}\,(\ell,i)$); Galois actions `galT` on each $\mathbb{T}.F\,\ell$; families $W\colon\mathrm{Fin}\,2\to\mathrm{SemilinearAut}(\overline{\mathbb{Q}},\bar F)$ and $W_T$ of semilinear automorphisms of the $\mathbb{T}.F\,\ell$; and a witness `tw` of type `ModuliTowerWitnessD` for all these data, which in particular provides a map `tw.rep` from places of $\bar F$ to fake elliptic curves over $\overline{\mathbb{Q}}$ whose `pt`-point over $\bar s$ is the point of $X$ attached to the place through $\mathfrak{M}.\mathrm{pointEquivPlace}$ and $e_{\mathfrak{M}}$, a map `tw.repT` from places of $\mathbb{T}.F\,\ell$ to pairs consisting of a fake elliptic curve and an extra level at $\ell$, surjective and injective up to isomorphism of such pairs, the normalisations of the base automorphisms of `gal`, `galT`, $W$ and $W_T$, the compatibility of restriction of places along the degeneracy maps with the underlying curves, and the remaining clauses of that structure.
--
--   Two further hypotheses are imposed. The first, `hEXH` (pointwise description of the correspondence): for every prime $\ell\notin\{q,q'\}$, every place $P$ of $\bar F$ and every fake elliptic curve $E$ over $\overline{\mathbb{Q}}$ whose `pt`-point over $\bar s$ is the $\overline{\mathbb{Q}}$-point of $\mathfrak{M}.C$ corresponding to $P$, followed by $e_{\mathfrak{M}}$ and the first projection, there exist $n\in\mathbb{N}$, extra levels $K_0,\dots,K_{n-1}$ at $\ell$ on $E$ (each a closed subgroup scheme stable under $\Lambda$, killed by $\ell$, finite flat of rank $\ell^2$ with fibres isomorphic to $(\mathbb{Z}/\ell)^2$, meeting the level-$N$ structure trivially), and places $Q_0,\dots,Q_{n-1}$ of $\bar F$ such that: (i) if $K_i$ and $K_j$ have the same $\overline{\mathbb{Q}}$-points, in the sense that a point of $E$ over the identity of $\operatorname{Spec}\overline{\mathbb{Q}}$ factors through $K_i$ if and only if it factors through $K_j$, then $i=j$; (ii) every extra level $K'$ at $\ell$ on $E$ has the same $\overline{\mathbb{Q}}$-points as some $K_i$; (iii) for each $i$ the pair $(E,K_i)$ admits an $\ell$-level isogeny to `tw.rep` $Q_i$, i.e. there are mutually dual morphisms $\phi,\psi$ over the base, multiplicative for the group laws on points, commuting with the $\Lambda$-actions, with $\phi$ followed by $\psi$ and $\psi$ followed by $\phi$ both equal to the action of $\ell$ whenever $\ell\in\Lambda$, with the points annihilated by $\phi$ being exactly those factoring through $K_i$, and with $\phi$ carrying level-$N$ structure points to level-$N$ structure points; and (iv) the divisor correspondence attached to $\mathbb{T}.\varphi\,(\ell,0)$ and $\mathbb{T}.\varphi\,(\ell,1)$ with their integrality witnesses, that is pullback along the first map followed by pushforward along the second, sends the divisor $[P]$ to $\sum_{i<n}[Q_i]$.
--
--   The second, `hSWAP₁` (transfer of extra levels of coprime level along an isogeny leg): for all distinct primes $\ell,\ell'$, all fake elliptic curves $E,E_1$ over $\overline{\mathbb{Q}}$, every extra level $K$ at $\ell$ on $E$, and all morphisms $\phi\colon E.A\to E_1.A$ and $\psi\colon E_1.A\to E.A$ over the base such that both are multiplicative on points, both commute with the $\Lambda$-actions, $\phi$ followed by $\psi$ and $\psi$ followed by $\phi$ are the action of $\ell$ whenever $\ell\in\Lambda$, $1\in\Lambda$, the points annihilated by $\phi$ are exactly those factoring through $K$, $\phi$ carries level-$N$ structure points to level-$N$ structure points, and every level-$N$ structure point of $E_1$ is the $\phi$-image of a level-$N$ structure point of $E$: then (a) each extra level $K'$ at $\ell'$ on $E$ has an image extra level $K_1'$ at $\ell'$ on $E_1$, characterised functorially by: a point of $E_1$ factors through $K_1'$ if and only if it is the $\phi$-image of a point factoring through $K'$; (b) each extra level $K_1'$ at $\ell'$ on $E_1$ arises in this way, on $\overline{\mathbb{Q}}$-points, from some extra level $K'$ at $\ell'$ on $E$; and (c) two extra levels $K',K''$ at $\ell'$ on $E$ have the same $\overline{\mathbb{Q}}$-points if and only if their $\phi$-images do.
--
--   The third, `hSWAP₂` (the two double quotients agree): for all distinct primes $\ell,\ell'$, fake elliptic curves $E,E_1,E_1',d,d'$ over $\overline{\mathbb{Q}}$, an extra level $K$ at $\ell$ and an extra level $K'$ at $\ell'$ on $E$, a pair $(\phi,\psi)$ between $E$ and $E_1$ satisfying the conditions listed above with respect to $\ell$ and $K$ (multiplicativity of both maps on points, $\Lambda$-equivariance of both, the two composites being the action of $\ell$ when $\ell\in\Lambda$, the points annihilated by $\phi$ being those factoring through $K$, and preservation of level-$N$ structure points), and a pair $(\phi',\psi')$ between $E$ and $E_1'$ satisfying the same conditions with respect to $\ell'$ and $K'$: if $K_1'$ is an extra level at $\ell'$ on $E_1$ whose $\overline{\mathbb{Q}}$-points are the $\phi$-images of the points of $K'$, and $K_1$ is an extra level at $\ell$ on $E_1'$ whose $\overline{\mathbb{Q}}$-points are the $\phi'$-images of the points of $K$, and if $d$ is the target of an $\ell'$-level isogeny from $(E_1,K_1')$ and $d'$ the target of an $\ell$-level isogeny from $(E_1',K_1)$, then $d$ and $d'$ are isomorphic as fake elliptic curves.
--
--   Under these hypotheses, for all primes $\ell,\ell'$ away from $q$ and $q'$ and every divisor $\mathcal{D}$ of $\bar F$ over $\overline{\mathbb{Q}}$ (a finitely supported $\mathbb{Z}$-valued function on the places), the two divisor correspondences commute on $\mathcal{D}$: applying the correspondence attached to $\mathbb{T}.\varphi\,(\ell',0)$, $\mathbb{T}.\varphi\,(\ell',1)$ and then the one attached to $\mathbb{T}.\varphi\,(\ell,0)$, $\mathbb{T}.\varphi\,(\ell,1)$ gives the same divisor as applying them in the opposite order, each correspondence being pullback along the $0$-th degeneracy map followed by pushforward along the $1$-st, with the integrality witnesses $\mathbb{T}.\mathrm{integral}$. The primes $\ell$ and $\ell'$ are not assumed distinct.
--
--   This is the commutativity of the Hecke correspondences $T_\ell$ and $T_{\ell'}$, for primes $\ell,\ell'$ away from the two ramified primes $q,q'$, acting on divisors of the geometric function field of the quaternionic (fake elliptic curve) moduli curve over $\mathbb{Z}[1/D]$; it is deduced from a pointwise description of each correspondence as a sum over extra levels and from the two transfer hypotheses for levels of coprime order. It feeds [`CerednikDrinfeld.QM.ModuliTowerWitnessD.correspondence_comm_of_two_mul_dvd_of_squarefree`](thm.html#CerednikDrinfeld.QM.ModuliTowerWitnessD.correspondence_comm_of_two_mul_dvd_of_squarefree), and thence the Hecke-equivariance bookkeeping used in the Čerednik–Drinfeld comparison of Shimura and modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_correspondence_comm_of_exhaustive_of_swap_of_two_mul_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMModuliTowerD

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.ModuliTowerWitnessD.correspondence_comm_of_exhaustive_of_swap_of_two_mul_dvd
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) (hD : 2 * N * q * q' ∣ D)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

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

    (𝕋 : HeckeTower.TowerData q q' Fbar)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) Fbar) (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (tw : ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT)

    (hEXH : ∀ (ℓ : HeckeTower.AwayPrime q q') (P : Place (AlgebraicClosure ℚ) Fbar) (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)),
      (pt _ sbar E).1 = (𝔐.pointEquivPlace.symm P).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar →
      ∃ (n : ℕ) (K : Fin n → E.ExtraLevel (ℓ.1 : ℕ)) (Q : Fin n → Place (AlgebraicClosure ℚ) Fbar),
        (∀ i j : Fin n,
            (∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough (K i).levK x ↔ FactorsThrough (K j).levK x) → i = j) ∧
        (∀ K' : E.ExtraLevel (ℓ.1 : ℕ), ∃ i : Fin n,
            ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough K'.levK x ↔ FactorsThrough (K i).levK x) ∧
        (∀ i : Fin n,
            FakeEllipticCurve.IsLevelIsogeny (ℓ.1 : ℕ)
              (⟨E, K i⟩ : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) (AlgebraicClosure ℚ)) (tw.rep (Q i))) ∧
        Divisor.correspondence (𝕋.φ (ℓ, 0)) (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 0)) (𝕋.integral (ℓ, 1)) (Finsupp.single P 1) =
          Finset.univ.sum (fun i : Fin n => Finsupp.single (Q i) 1))

    (hSWAP₁ : ∀ (ℓ ℓ' : ℕ) [Fact ℓ.Prime] [Fact ℓ'.Prime], ℓ ≠ ℓ' →
      ∀ (E E₁ : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)) (K : E.ExtraLevel ℓ)
        (φ : E.A ⟶ E₁.A) (hφ : φ ≫ E₁.f = E.f) (ψ : E₁.A ⟶ E.A) (hψ : ψ ≫ E.f = E₁.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
          mapPt φ hφ (E.L.mul t P Q) = E₁.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E₁.f),
          mapPt ψ hψ (E₁.L.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) →
        (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E₁.act x) → (∀ x : ↥Λ, E₁.act x ≫ ψ = ψ ≫ E.act x) →
        (∀ hℓ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
          φ ≫ ψ = E.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩ ∧ ψ ≫ φ = E₁.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩) →
        (1 : ℍ[ℚ, a, b]) ∈ Λ →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
          mapPt φ hφ P = E₁.L.one t ↔ FactorsThrough K.levK P) →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
          FactorsThrough E.lev P → FactorsThrough E₁.lev (mapPt φ hφ P)) →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (x : SchemeHomOver t E₁.f),
          FactorsThrough E₁.lev x → ∃ P : SchemeHomOver t E.f, FactorsThrough E.lev P ∧ mapPt φ hφ P = x) →
        (∀ K' : E.ExtraLevel ℓ', ∃ K₁' : E₁.ExtraLevel ℓ',
          ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (x : SchemeHomOver t E₁.f),
            FactorsThrough K₁'.levK x ↔ ∃ y : SchemeHomOver t E.f, FactorsThrough K'.levK y ∧ mapPt φ hφ y = x) ∧
        (∀ K₁' : E₁.ExtraLevel ℓ', ∃ K' : E.ExtraLevel ℓ',
          ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E₁.f,
            FactorsThrough K₁'.levK x ↔ ∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough K'.levK y ∧ mapPt φ hφ y = x) ∧
        (∀ K' K'' : E.ExtraLevel ℓ',
          (∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough K'.levK y ↔ FactorsThrough K''.levK y) ↔
          (∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E₁.f,
              (∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough K'.levK y ∧ mapPt φ hφ y = x) ↔
              (∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough K''.levK y ∧ mapPt φ hφ y = x))))

    (hSWAP₂ : ∀ (ℓ ℓ' : ℕ) [Fact ℓ.Prime] [Fact ℓ'.Prime], ℓ ≠ ℓ' →
      ∀ (E E₁ E₁' d d' : FakeEllipticCurve Λ N (AlgebraicClosure ℚ)) (K : E.ExtraLevel ℓ) (K' : E.ExtraLevel ℓ')
        (φ : E.A ⟶ E₁.A) (hφ : φ ≫ E₁.f = E.f) (ψ : E₁.A ⟶ E.A) (hψ : ψ ≫ E.f = E₁.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
          mapPt φ hφ (E.L.mul t P Q) = E₁.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E₁.f),
          mapPt ψ hψ (E₁.L.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) →
        (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E₁.act x) → (∀ x : ↥Λ, E₁.act x ≫ ψ = ψ ≫ E.act x) →
        (∀ hℓ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
          φ ≫ ψ = E.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩ ∧ ψ ≫ φ = E₁.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩) →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
          mapPt φ hφ P = E₁.L.one t ↔ FactorsThrough K.levK P) →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
          FactorsThrough E.lev P → FactorsThrough E₁.lev (mapPt φ hφ P)) →
      ∀ (φ' : E.A ⟶ E₁'.A) (hφ' : φ' ≫ E₁'.f = E.f) (ψ' : E₁'.A ⟶ E.A) (hψ' : ψ' ≫ E.f = E₁'.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
          mapPt φ' hφ' (E.L.mul t P Q) = E₁'.L.mul t (mapPt φ' hφ' P) (mapPt φ' hφ' Q)) →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E₁'.f),
          mapPt ψ' hψ' (E₁'.L.mul t P Q) = E.L.mul t (mapPt ψ' hψ' P) (mapPt ψ' hψ' Q)) →
        (∀ x : ↥Λ, E.act x ≫ φ' = φ' ≫ E₁'.act x) → (∀ x : ↥Λ, E₁'.act x ≫ ψ' = ψ' ≫ E.act x) →
        (∀ hℓ : ((ℓ' : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
          φ' ≫ ψ' = E.act ⟨((ℓ' : ℚ) : ℍ[ℚ, a, b]), hℓ⟩ ∧ ψ' ≫ φ' = E₁'.act ⟨((ℓ' : ℚ) : ℍ[ℚ, a, b]), hℓ⟩) →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
          mapPt φ' hφ' P = E₁'.L.one t ↔ FactorsThrough K'.levK P) →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P : SchemeHomOver t E.f),
          FactorsThrough E.lev P → FactorsThrough E₁'.lev (mapPt φ' hφ' P)) →
      ∀ (K₁' : E₁.ExtraLevel ℓ'),
        (∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E₁.f,
          FactorsThrough K₁'.levK x ↔ ∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough K'.levK y ∧ mapPt φ hφ y = x) →
      ∀ (K₁ : E₁'.ExtraLevel ℓ),
        (∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E₁'.f,
          FactorsThrough K₁.levK x ↔ ∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough K.levK y ∧ mapPt φ' hφ' y = x) →
        FakeEllipticCurve.IsLevelIsogeny ℓ' (⟨E₁, K₁'⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ' (AlgebraicClosure ℚ)) d →
        FakeEllipticCurve.IsLevelIsogeny ℓ (⟨E₁', K₁⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ (AlgebraicClosure ℚ)) d' →
        FakeEllipticCurve.Iso d d')
    (ℓ ℓ' : HeckeTower.AwayPrime q q') (D : Divisor (AlgebraicClosure ℚ) Fbar) :
    Divisor.correspondence (𝕋.φ (ℓ, 0)) (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 0)) (𝕋.integral (ℓ, 1))
      (Divisor.correspondence (𝕋.φ (ℓ', 0)) (𝕋.φ (ℓ', 1)) (𝕋.integral (ℓ', 0)) (𝕋.integral (ℓ', 1)) D) =
    Divisor.correspondence (𝕋.φ (ℓ', 0)) (𝕋.φ (ℓ', 1)) (𝕋.integral (ℓ', 0)) (𝕋.integral (ℓ', 1))
      (Divisor.correspondence (𝕋.φ (ℓ, 0)) (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 0)) (𝕋.integral (ℓ, 1)) D) := by sorry
