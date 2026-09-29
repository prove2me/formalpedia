-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_meromorphicRealization_of_periodMap_of_analyticAt_evalAt_of_two_mul_dvd
-- name    : CerednikDrinfeld.QM.exists_meromorphicRealization_of_periodMap_of_analyticAt_evalAt_of_two_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/d87bdf4a-6b23-594a-b03e-f031e6185703
-- title:
--   Meromorphic realisation of the function field along a period map
-- statement:
--   Fix a squarefree $N$ and distinct primes $q,q'$ not dividing $N$, and $D$ with $2Nqq'\mid D$. Let $a,b\in\mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`: $0<a$ or $0<b$, and a finite place $v$ of $\mathbb{Q}$ has $\mathbb{H}[\mathbb{Q},a,b]\otimes\mathbb{Q}_v$ a division algebra exactly when $v$ lies above $q$ or $q'$. Let $\Lambda$ be a maximal order, $R\le\Lambda$ an Eichler order of level $N$ (an intersection of two maximal orders of relative index $N$), and $\iota$ an injective $\mathbb{Q}$-algebra map into $M_2(\mathbb{R})$, with $\Gamma=$ `fuchsianGroup R ι`, the determinant-one part of the image of the unit group of $R$. Further data, summarised here: an integral scheme $X$ smooth and proper of relative dimension $1$ over $\mathbb{Z}[1/D]$ with geometrically integral fibres, carrying a point rule `pt` on `FakeEllipticCurve Λ N` that is isomorphism-invariant, compatible with base change, and bijective on algebraically closed fields; a curve field $F_0$ over $\mathbb{C}$ with a `UniformizedHeckeCurve` structure $U_0$ for $\Gamma$ whose clauses ($h_0$) give surjectivity of $U_0.\mathrm{pt}$, a quaternionic description of the Hecke points by elements of $R$ of reduced norm $\ell$ matching `levelHeckeUSet`/`primeHeckeSet`, and the fact that $U_0.\mathrm{realize}$ is a $\Gamma$-invariant meromorphic realisation of $F_0$ identifying $F_0$ with all $\Gamma$-invariant meromorphic functions on $\mathfrak{H}$; a $\mathbb{C}$-point $s_{\mathbb{C}}$ of the base and a curve field $F_{\mathbb{C}}$ over $\mathbb{C}$ with a `CurveModel` $\mathfrak{M}_{\mathbb{C}}$ isomorphic, over the base, to the fibre $X\times_{s_{\mathbb{C}}}\mathbb{C}$. Given in addition a period map $\mathrm{per}$ from fake elliptic curves over $\mathbb{C}$ to $\mathfrak{H}$ with $E\cong E'$ iff $U_0.\mathrm{pt}(\mathrm{per}\,E)=U_0.\mathrm{pt}(\mathrm{per}\,E')$ and every $U_0.\mathrm{pt}(\tau)$ of this form; the holomorphy hypothesis that for $\tau_0$, $E_0$ and a place $\mathfrak{P}_0$ of $F_{\mathbb{C}}$ corresponding under $\mathfrak{M}_{\mathbb{C}}.\mathrm{pointEquivPlace}$ to the point $\mathrm{pt}(E_0)$, with $U_0.\mathrm{pt}(\tau_0)=U_0.\mathrm{pt}(\mathrm{per}\,E_0)$, each $x$ in the valuation ring of $\mathfrak{P}_0$ admits $F$ analytic at $\tau_0$ with $x$ regular at, and $F(\tau)$ equal to, the value $\mathfrak{P}.\mathrm{evalAt}\,x$ at every nearby $\tau$ corresponding to some $E$, $\mathfrak{P}$; and the discreteness hypothesis that each $\Gamma$-orbit is eventually avoided on punctured neighbourhoods: then there exists $V:F_{\mathbb{C}}\to\mathfrak{H}\to\mathbb{C}$ such that (i) whenever $\mathrm{pt}(E)$ corresponds to the place $\mathfrak{P}$, $x$ lies in the valuation ring of $\mathfrak{P}$ and $U_0.\mathrm{pt}(\tau)=U_0.\mathrm{pt}(\mathrm{per}\,E)$, one has $V\,x\,\tau=\mathfrak{P}.\mathrm{evalAt}\,x$; (ii) for such $E$, $\mathfrak{P}$, $\tau$, membership of $x$ in the valuation ring of $\mathfrak{P}$ is equivalent to $\|V\,x\|$ being bounded near $\tau$ on a punctured neighbourhood; and (iii) each $V\,x$ is meromorphic at every point of $\mathfrak{H}$ (read through `UpperHalfPlane.ofComplex`), and, on punctured neighbourhoods, $V$ is additive, multiplicative, sends a scalar $c\in\mathbb{C}$ to the constant $c$, and is $\Gamma$-invariant.
--
--   This is the analytic half of the complex uniformisation of the Shimura curve attached to an Eichler order of level $N$ in an indefinite quaternion algebra ramified exactly at $q$ and $q'$: it turns a period map with holomorphic classifying map into a meromorphic, $\Gamma$-invariant realisation of the function field of the coarse moduli curve on the upper half-plane, with the valuation rings of places read off by boundedness. It feeds the assembly of the period-map statement [`CerednikDrinfeld.QM.exists_periodMap_meromorphicRealization_of_uniformizedHeckeCurve_of_two_mul_dvd`](thm.html#CerednikDrinfeld.QM.exists_periodMap_meromorphicRealization_of_uniformizedHeckeCurve_of_two_mul_dvd), the identification of places being supplied by [`AlgebraicCurve.CurveModel.place_eq_of_pointEquivPlace_symm_comp_eq`](thm.html#AlgebraicCurve.CurveModel.place_eq_of_pointEquivPlace_symm_comp_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_meromorphicRealization_of_periodMap_of_analyticAt_evalAt_of_two_mul_dvd.lean

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

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology

theorem CerednikDrinfeld.QM.exists_meromorphicRealization_of_periodMap_of_analyticAt_evalAt_of_two_mul_dvd
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
    (he𝔐c_snd : e𝔐c ≫ CategoryTheory.Limits.pullback.snd πX sC = 𝔐c.toBase)

    (perE : FakeEllipticCurve Λ N ℂ → UpperHalfPlane)
    (hper :

      (∀ E E' : FakeEllipticCurve Λ N ℂ,
        FakeEllipticCurve.Iso E E' ↔ U₀.pt (perE E) = U₀.pt (perE E')) ∧

      (∀ τ : UpperHalfPlane, ∃ E : FakeEllipticCurve Λ N ℂ, U₀.pt (perE E) = U₀.pt τ))

    (hhol : ∀ (τ₀ : UpperHalfPlane) (E₀ : FakeEllipticCurve Λ N ℂ) (𝔓₀ : Place ℂ Fc),
      (pt _ sC E₀).1 = (𝔐c.pointEquivPlace.symm 𝔓₀).1 ≫ e𝔐c ≫ CategoryTheory.Limits.pullback.fst πX sC →
      U₀.pt τ₀ = U₀.pt (perE E₀) →
      ∀ x : Fc, x ∈ 𝔓₀.toValuationSubring →
        ∃ F : ℂ → ℂ, AnalyticAt ℂ F (τ₀ : ℂ) ∧
          ∀ᶠ τ in 𝓝 τ₀, ∀ (E : FakeEllipticCurve Λ N ℂ) (𝔓 : Place ℂ Fc),
            (pt _ sC E).1 = (𝔐c.pointEquivPlace.symm 𝔓).1 ≫ e𝔐c ≫ CategoryTheory.Limits.pullback.fst πX sC →
            U₀.pt τ = U₀.pt (perE E) → x ∈ 𝔓.toValuationSubring ∧ F (τ : ℂ) = 𝔓.evalAt x)

    (hdisc : ∀ τ τ' : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, ¬ ∃ γ ∈ fuchsianGroup R ι, γ • τ' = z) :
    ∃ V : Fc → UpperHalfPlane → ℂ,

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
