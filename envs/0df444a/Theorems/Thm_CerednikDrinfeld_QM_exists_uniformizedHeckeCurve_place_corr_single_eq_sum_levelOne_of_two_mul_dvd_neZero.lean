-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_uniformizedHeckeCurve_place_corr_single_eq_sum_levelOne_of_two_mul_dvd_neZero
-- name    : CerednikDrinfeld.QM.exists_uniformizedHeckeCurve_place_corr_single_eq_sum_levelOne_of_two_mul_dvd_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/ea86892f-816e-5ee3-94f3-3bc40c5fe817
-- title:
--   Complex uniformisation of the level-one fake elliptic moduli curve
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that $\mathbb H[\mathbb Q,a,b]$ is indefinite ($0<a$ or $0<b$) and, for every finite place $v$ of $\mathbb Q$, its completion at $v$ is a division algebra exactly when $v$ lies over $q$ or $q'$; let $\Lambda$ be a maximal order (an order of $\mathbb H[\mathbb Q,a,b]$ maximal among orders), $\iota$ an injective $\mathbb Q$-algebra map $\mathbb H[\mathbb Q,a,b] \to M_2(\mathbb R)$, and $D$ a nonzero natural number with $2qq' \mid D$. Suppose given an integral scheme $X$ with a morphism $\pi_X$ to $\operatorname{Spec}$ of `Localization.Away` $(D : \mathbb Z)$, smooth, proper and smooth of relative dimension $1$, with integral fibres over every point of the base valued in an algebraically closed field, together with an assignment `pt` sending each fake elliptic curve with $\Lambda$-action and level $1$ over a ring $S$, relative to an $S$-point $s$ of the base, to a point of $X$ over $s$; `pt` is assumed invariant under isomorphism of fake elliptic curves, compatible with pullback along ring homomorphisms over the base, and, over algebraically closed fields, surjective onto points of $X$ and injective up to isomorphism. Suppose also given a $\overline{\mathbb Q}$-point $\bar s$ of the base compatible with the $\mathbb Z$-structure, a field $F$ over $\overline{\mathbb Q}$ which is a curve over $\overline{\mathbb Q}$ (principal divisors, finite residue extensions, $\Omega_{F/\overline{\mathbb Q}}$ free of rank one) and essentially of finite type, a homomorphism $\mathrm{gal}$ from the $\mathbb Q$-automorphisms of $\overline{\mathbb Q}$ to the semilinear automorphisms of $F$, and a curve model $\mathfrak M$ of $F$ together with an isomorphism $e_{\mathfrak M}$ from $\mathfrak M.C$ to the fibre of $\pi_X$ at $\bar s$ compatible with the structure morphisms. The conclusion asserts the existence of a field $F_c$ over $\mathbb C$, again a curve over $\mathbb C$ and essentially of finite type, of a `UniformizedHeckeCurve` $U$ for the Fuchsian group `fuchsianGroup` $\Lambda$ $\iota$ (the image in $GL_2(\mathbb R)$ of the unit group of $\Lambda$ intersected with the kernel of the determinant), and of a map $\mathrm{bcPlace}$ from places of $F/\overline{\mathbb Q}$ to places of $F_c/\mathbb C$, with the following properties: $U.\mathrm{pt} : \mathbb H \to \mathrm{Place}(\mathbb C, F_c)$ is surjective; for every prime $\ell$ there is a finite set $S$ of elements of $\Lambda$ of reduced norm $\ell$, each of which, tensored with $1$, represents an element of `levelHeckeUSet` $\Lambda$ $\Lambda$ $\ell$ or of `primeHeckeSet` $\Lambda$ $\ell$ according as $\ell \mid 1$ or not, such that every $y \in \Lambda$ of reduced norm $\ell$ with such a representative is $u \cdot x$ for a unique $x \in S$ and some unit $u$ of $\Lambda$ of reduced norm $1$, and such that $U.\mathrm{heckePoints}\,\ell$, pushed into $M_2(\mathbb R)$, is the image of $S$ under $\iota$; nine analytic clauses expressing that $U.\mathrm{realize}$ realises $F_c$ as the field of $\Gamma$-invariant meromorphic functions on $\mathbb H$ (meromorphy at every point, additivity, multiplicativity, constants, separation of elements of $F_c$, invariance under the Fuchsian group, and surjectivity onto invariant meromorphic functions, all identities holding on a punctured neighbourhood filter); injectivity of $\mathrm{bcPlace}$; for each prime $\ell \notin \{q,q'\}$, each place $P$ and each fake elliptic curve $E$ over $\overline{\mathbb Q}$ whose moduli point is the point of $X$ attached to $P$ through $\mathfrak M.\mathrm{pointEquivPlace}$, $e_{\mathfrak M}$ and the first pullback projection, the existence of $n$, of extra $\ell$-level structures $K_i$ on $E$, quotients $d_i$ and places $P_i$ such that the $K_i$ are pairwise inequivalent and exhaust all extra $\ell$-levels (equivalence being agreement of which points factor through $\mathrm{levK}$), each $(E,K_i)$ is an $\ell$-level isogeny onto $d_i$, each $d_i$ has moduli point attached to $P_i$, and $U.\mathrm{corr}\,\ell$ sends the divisor $\mathrm{bcPlace}(P)$ to $\sum_i \mathrm{bcPlace}(P_i)$; and, at $q$ and at $q'$, that whenever $E, E'$ have moduli points attached to places $P, Q$ and $E'$ is an Atkin–Lehner quotient of $E$ at that prime, $U.\mathrm{corr}$ at that prime sends $\mathrm{bcPlace}(P)$ to $\mathrm{bcPlace}(Q)$.
--
--   This is the level-one case ($N = 1$, Eichler order equal to the maximal order $\Lambda$) of the complex uniformisation of the Shimura curve attached to an indefinite quaternion algebra over $\mathbb Q$ ramified exactly at $q$ and $q'$, stated over the base $\mathbb Z[1/D]$ for any $D$ divisible by $2qq'$ and phrased so that the dictionary between $\overline{\mathbb Q}$-places of the geometric function field and places of the analytic model is compatible with the Hecke correspondences away from $qq'$ and with the Atkin–Lehner quotients at $q$ and $q'$. It feeds the finiteness statement for fake elliptic curves with prescribed extra structure used on the way to the Čerednik–Drinfeld comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_uniformizedHeckeCurve_place_corr_single_eq_sum_levelOne_of_two_mul_dvd_neZero.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld.QM
open CerednikDrinfeld
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology

theorem CerednikDrinfeld.QM.exists_uniformizedHeckeCurve_place_corr_single_eq_sum_levelOne_of_two_mul_dvd_neZero
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (hqq' : q' ≠ q)
    (D : ℕ) [NeZero D] (hD : 2 * q * q' ∣ D)

    (X : Scheme.{0}) [hXint : IsIntegral X]
    (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ 1 S → SchemeHomOver s πX)
    (hsmooth : Smooth πX) (hproper : IsProper πX)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ _) (E E' : FakeEllipticCurve Λ 1 S),
      FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ _) (s' : Spec (CommRingCat.of S') ⟶ _),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ 1 S) (E' : FakeEllipticCurve Λ 1 S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _) (P : SchemeHomOver s πX),
      ∃ E : FakeEllipticCurve Λ 1 k, pt k s E = P)
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ _)
      (E E' : FakeEllipticCurve Λ 1 k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')
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
    (he𝔐_snd : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase) :
    ∃ (Fc : Type) (_ : Field Fc) (_ : Algebra ℂ Fc) (_ : AlgebraicCurve.IsCurveOver ℂ Fc)
      (_ : Algebra.EssFiniteType ℂ Fc) (U : ModularCurve.UniformizedHeckeCurve (fuchsianGroup Λ ι) Fc)
      (bcPlace : Place (AlgebraicClosure ℚ) Fbar → Place ℂ Fc),

      Function.Surjective U.pt ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ∃ S : Finset ℍ[ℚ, a, b],
        (∀ x ∈ S, x ∈ Λ ∧ nrd x = ℓ ∧
          ∃ h ∈ (if ℓ ∣ 1 then levelHeckeUSet Λ Λ ℓ else primeHeckeSet Λ ℓ),
            (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = x ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) ∧
        (∀ y : ℍ[ℚ, a, b], y ∈ Λ → nrd y = ℓ →
          (∃ h ∈ (if ℓ ∣ 1 then levelHeckeUSet Λ Λ ℓ else primeHeckeSet Λ ℓ),
            (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = y ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) →
          ∃! x, x ∈ S ∧ ∃ u : ℍ[ℚ, a, b], IsUnitOf Λ u ∧ nrd u = 1 ∧ u * x = y) ∧
        (U.heckePoints ℓ hℓ).map (fun g => (g : Matrix (Fin 2) (Fin 2) ℝ)) = S.val.map ι) ∧
      (∀ (x : Fc) (τ : UpperHalfPlane), MeromorphicAt (fun z : ℂ => U.realize x (UpperHalfPlane.ofComplex z)) (τ : ℂ)) ∧
      (∀ (x y : Fc) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, U.realize (x + y) z = U.realize x z + U.realize y z) ∧
      (∀ (x y : Fc) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, U.realize (x * y) z = U.realize x z * U.realize y z) ∧
      (∀ (c : ℂ) (τ : UpperHalfPlane), ∀ᶠ z in 𝓝[≠] τ, U.realize (algebraMap ℂ Fc c) z = c) ∧
      (∀ x y : Fc, (∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, U.realize x z = U.realize y z) → x = y) ∧
      (∀ x : Fc, ∀ γ ∈ fuchsianGroup Λ ι, ∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, U.realize x (γ • z) = U.realize x z) ∧
      (∀ f : UpperHalfPlane → ℂ, (∀ τ : UpperHalfPlane, MeromorphicAt (fun z : ℂ => f (UpperHalfPlane.ofComplex z)) (τ : ℂ)) →
        (∀ γ ∈ fuchsianGroup Λ ι, ∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, f (γ • z) = f z) →
        ∃ x : Fc, ∀ τ : UpperHalfPlane, ∀ᶠ z in 𝓝[≠] τ, U.realize x z = f z) ∧

      Function.Injective bcPlace ∧

      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ≠ q → ℓ ≠ q' →
        ∀ (P : Place (AlgebraicClosure ℚ) Fbar) (E : FakeEllipticCurve Λ 1 (AlgebraicClosure ℚ)),
          (pt _ sbar E).1 = (𝔐.pointEquivPlace.symm P).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar →
          ∃ (n : ℕ) (K : Fin n → E.ExtraLevel ℓ) (d : Fin n → FakeEllipticCurve Λ 1 (AlgebraicClosure ℚ))
            (Ps : Fin n → Place (AlgebraicClosure ℚ) Fbar),
            (∀ i j : Fin n,
                (∀ x : SchemeHomOver (CategoryTheory.CategoryStruct.id (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f,
                  FactorsThrough (K i).levK x ↔ FactorsThrough (K j).levK x) → i = j) ∧
            (∀ K' : E.ExtraLevel ℓ, ∃ i : Fin n,
                ∀ x : SchemeHomOver (CategoryTheory.CategoryStruct.id (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f,
                  FactorsThrough K'.levK x ↔ FactorsThrough (K i).levK x) ∧
            (∀ i : Fin n, FakeEllipticCurve.IsLevelIsogeny ℓ
                (⟨E, K i⟩ : FakeEllipticCurve.WithExtraLevel Λ 1 ℓ (AlgebraicClosure ℚ)) (d i)) ∧
            (∀ i : Fin n, (pt _ sbar (d i)).1 = (𝔐.pointEquivPlace.symm (Ps i)).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar) ∧
            U.corr ℓ hℓ (Finsupp.single (bcPlace P) 1) =
              Finset.univ.sum (fun i : Fin n => Finsupp.single (bcPlace (Ps i)) 1)) ∧

      (∀ (P Q : Place (AlgebraicClosure ℚ) Fbar) (E E' : FakeEllipticCurve Λ 1 (AlgebraicClosure ℚ)),
        (pt _ sbar E).1 = (𝔐.pointEquivPlace.symm P).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar →
        (pt _ sbar E').1 = (𝔐.pointEquivPlace.symm Q).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar →
        E.IsAtkinLehnerQuotient q E' →
        U.corr q Fact.out (Finsupp.single (bcPlace P) 1) = Finsupp.single (bcPlace Q) 1) ∧
      (∀ (P Q : Place (AlgebraicClosure ℚ) Fbar) (E E' : FakeEllipticCurve Λ 1 (AlgebraicClosure ℚ)),
        (pt _ sbar E).1 = (𝔐.pointEquivPlace.symm P).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar →
        (pt _ sbar E').1 = (𝔐.pointEquivPlace.symm Q).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar →
        E.IsAtkinLehnerQuotient q' E' →
        U.corr q' Fact.out (Finsupp.single (bcPlace P) 1) = Finsupp.single (bcPlace Q) 1) := by sorry
