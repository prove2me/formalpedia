-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_periodMap_meromorphicRealization_of_uniformizedHeckeCurve_of_two_mul_dvd
-- name    : CerednikDrinfeld.QM.exists_periodMap_meromorphicRealization_of_uniformizedHeckeCurve_of_two_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/a4df070d-0ad5-54f1-87ba-9d0c67421a4e
-- title:
--   Period map and meromorphic realisation on a Shimura curve
-- statement:
--   Fix $N$ nonzero, primes $q \ne q'$ neither dividing $N$, and $D$ with $2Nqq' \mid D$; let $\mathbb{H}[\mathbb{Q},a,b]$ be indefinite ($0 < a$ or $0 < b$) and ramified exactly at the places above $q$ and $q'$, let $\Lambda$ be a maximal order, $N$ squarefree, $R \le \Lambda$ an Eichler order of level $N$ (an intersection of two maximal orders of relative index $N$), and $\iota$ an injective $\mathbb{Q}$-algebra map into $M_2(\mathbb{R})$. Assume given an integral scheme $X$, a smooth proper morphism $\pi_X$ of relative dimension $1$ to $\mathrm{Spec}\,\mathbb{Z}[1/D]$ with geometrically integral fibres, and a rule `pt` assigning to every fake elliptic curve for $(\Lambda,N)$ over a base $S$ a point of $X$ over $S$, invariant under isomorphism, compatible with base change, and bijective on isomorphism classes over algebraically closed fields. Assume further a uniformized Hecke curve $U_0$ for the Fuchsian group $\iota(R^\times) \cap \mathrm{SL}$ on a curve $F_{c_0}/\mathbb{C}$ whose point map is surjective, whose Hecke multisets at each prime $\ell$ are the images under $\iota$ of a transversal of norm-$\ell$ elements of $R$ represented by `levelHeckeUSet` at $\ell \mid N$ and by `primeHeckeSet` otherwise, and whose realisation map is a $\Gamma$-invariant meromorphic, additive, multiplicative, $\mathbb{C}$-constant, injective and surjective identification of $F_{c_0}$ with the field of $\Gamma$-invariant meromorphic functions on $\mathbb{H}$; and a $\mathbb{C}$-point $s_{\mathbb{C}}$ of the base together with a curve model $\mathfrak{M}_c$ of a field $F_c/\mathbb{C}$ and an isomorphism $e_{\mathfrak{M}_c}$ of $\mathfrak{M}_c.C$ with the fibre $X \times s_{\mathbb{C}}$ over the base. Then there exist a period map $\mathrm{perE}$ from fake elliptic curves over $\mathbb{C}$ to $\mathbb{H}$ and a map $V : F_c \to (\mathbb{H} \to \mathbb{C})$ such that: two fake elliptic curves are isomorphic precisely when their periods give the same place $U_0.\mathrm{pt}$; every $\tau \in \mathbb{H}$ arises from some fake elliptic curve; for each prime $\ell \notin \{q,q'\}$ and each $E$ the multiset of places $U_0.\mathrm{pt}(\delta \cdot \mathrm{perE}\,E)$ over the Hecke multiset at $\ell$ equals the multiset of places of the $\ell$-isogeny quotients of $E$ indexed by its finitely many extra $\ell$-level subgroups, listed without repetition and exhausting all of them; at $q$ and at $q'$ the corresponding Hecke multiset is the single place of the Atkin–Lehner quotient; for $x \in F_c$ and a place $\mathfrak{P}$ corresponding under $\mathfrak{M}_c.\mathrm{pointEquivPlace}$ and $e_{\mathfrak{M}_c}$ to the point $\mathrm{pt}(E)$, the value $V\,x\,\tau$ at any $\tau$ with $U_0.\mathrm{pt}\,\tau = U_0.\mathrm{pt}(\mathrm{perE}\,E)$ equals $\mathfrak{P}.\mathrm{evalAt}\,x$ whenever $x$ lies in the valuation ring of $\mathfrak{P}$, and membership in that valuation ring is equivalent to $\|V\,x\|$ being bounded near $\tau$ along the punctured neighbourhood filter; and $V$ is meromorphic at every point of $\mathbb{H}$, additive, multiplicative, constant on scalars from $\mathbb{C}$, and invariant under the Fuchsian group, all these identities holding eventually on punctured neighbourhoods.
--
--   This is the complex-analytic uniformisation of the Shimura curve attached to an Eichler order of squarefree level $N$ in an indefinite quaternion algebra ramified exactly at $q$ and $q'$: the period map identifies isomorphism classes of fake elliptic curves over $\mathbb{C}$ with $\Gamma$-orbits in $\mathbb{H}$, transports Hecke and Atkin–Lehner correspondences into the Hecke multisets of the uniformized curve, and realises the function field of the fibre at $\mathbb{C}$ as $\Gamma$-invariant meromorphic functions whose values at moduli points are the values of the corresponding rational function. It is used to transfer the algebraic moduli description of the Shimura curve over $\mathbb{Z}[1/D]$ to the automorphic side, and feeds the comparison of places with base change on the uniformized Hecke curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_periodMap_meromorphicRealization_of_uniformizedHeckeCurve_of_two_mul_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open AlgebraicCurve
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology

theorem CerednikDrinfeld.QM.exists_periodMap_meromorphicRealization_of_uniformizedHeckeCurve_of_two_mul_dvd
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

    (sC : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (Fc : Type) [Field Fc] [Algebra ℂ Fc] [AlgebraicCurve.IsCurveOver ℂ Fc] [Algebra.EssFiniteType ℂ Fc]
    (𝔐c : AlgebraicCurve.CurveModel ℂ Fc)
    (e𝔐c : 𝔐c.C ⟶ CategoryTheory.Limits.pullback πX sC) (he𝔐c : IsIso e𝔐c)
    (he𝔐c_snd : e𝔐c ≫ CategoryTheory.Limits.pullback.snd πX sC = 𝔐c.toBase) :
    ∃ (perE : FakeEllipticCurve Λ N ℂ → UpperHalfPlane) (V : Fc → UpperHalfPlane → ℂ),

      (∀ E E' : FakeEllipticCurve Λ N ℂ,
        FakeEllipticCurve.Iso E E' ↔ U₀.pt (perE E) = U₀.pt (perE E')) ∧

      (∀ τ : UpperHalfPlane, ∃ E : FakeEllipticCurve Λ N ℂ, U₀.pt (perE E) = U₀.pt τ) ∧

      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ≠ q → ℓ ≠ q' → ∀ E : FakeEllipticCurve Λ N ℂ,
        ∃ (n : ℕ) (K : Fin n → E.ExtraLevel ℓ) (d : Fin n → FakeEllipticCurve Λ N ℂ),
            (∀ i j : Fin n,
                (∀ x : SchemeHomOver (CategoryTheory.CategoryStruct.id (Spec (CommRingCat.of ℂ))) E.f,
                  FactorsThrough (K i).levK x ↔ FactorsThrough (K j).levK x) → i = j) ∧
            (∀ K' : E.ExtraLevel ℓ, ∃ i : Fin n,
                ∀ x : SchemeHomOver (CategoryTheory.CategoryStruct.id (Spec (CommRingCat.of ℂ))) E.f,
                  FactorsThrough K'.levK x ↔ FactorsThrough (K i).levK x) ∧
            (∀ i : Fin n, FakeEllipticCurve.IsLevelIsogeny ℓ
                (⟨E, K i⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ ℂ) (d i)) ∧
            ((U₀.heckePoints ℓ hℓ).map (fun δ => U₀.pt (δ • perE E))) =
              (Finset.univ.val.map (fun i : Fin n => U₀.pt (perE (d i))))) ∧

      (∀ E E' : FakeEllipticCurve Λ N ℂ, E.IsAtkinLehnerQuotient q E' →
        ((U₀.heckePoints q Fact.out).map (fun δ => U₀.pt (δ • perE E))) = {U₀.pt (perE E')}) ∧
      (∀ E E' : FakeEllipticCurve Λ N ℂ, E.IsAtkinLehnerQuotient q' E' →
        ((U₀.heckePoints q' Fact.out).map (fun δ => U₀.pt (δ • perE E))) = {U₀.pt (perE E')}) ∧

      (∀ (x : Fc) (𝔓 : Place ℂ Fc) (E : FakeEllipticCurve Λ N ℂ),
        (pt _ sC E).1 = (𝔐c.pointEquivPlace.symm 𝔓).1 ≫ e𝔐c ≫ CategoryTheory.Limits.pullback.fst πX sC →
        x ∈ 𝔓.toValuationSubring → ∀ τ : UpperHalfPlane, U₀.pt τ = U₀.pt (perE E) → V x τ = 𝔓.evalAt x) ∧

      (∀ (x : Fc) (𝔓 : Place ℂ Fc) (E : FakeEllipticCurve Λ N ℂ),
      (pt _ sC E).1 = (𝔐c.pointEquivPlace.symm 𝔓).1 ≫ e𝔐c ≫ CategoryTheory.Limits.pullback.fst πX sC →
      ∀ τ : UpperHalfPlane, U₀.pt τ = U₀.pt (perE E) →
        (x ∈ 𝔓.toValuationSubring ↔
          Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : UpperHalfPlane => ‖V x z‖))) ∧

      ((∀ (x : Fc) (τ : UpperHalfPlane), MeromorphicAt (fun z : ℂ => V x (UpperHalfPlane.ofComplex z)) (τ : ℂ)) ∧
      (∀ (x y : Fc) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, V (x + y) z = V x z + V y z) ∧
      (∀ (x y : Fc) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, V (x * y) z = V x z * V y z) ∧
      (∀ (c : ℂ) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, V (algebraMap ℂ Fc c) z = c) ∧
      (∀ x : Fc, ∀ γ ∈ fuchsianGroup R ι, ∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, V x (γ • z) = V x z)) := by sorry
