-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_exists_algEquiv_level_comp_phi_eq_of_pt_pullback_of_two_mul_dvd
-- name    : CerednikDrinfeld.QM.ModuliTowerWitnessD.exists_algEquiv_level_comp_phi_eq_of_pt_pullback_of_two_mul_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/73e93ba9-0248-5838-8e57-67bfd8eb769c
-- title:
--   Level-(N;ℓ) tower field is the function field of the coarse moduli curve
-- statement:
--   Fix naturals $N,q,q'$ with $N \neq 0$, $q$ and $q'$ prime, $q \nmid N$, $q' \nmid N$, $q' \neq q$, and $D$ with $2Nqq' \mid D$; rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0 < a$ or $0 < b$ and, for each finite place $v$ of $\mathbb{Q}$, the completion $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra exactly when $v$ lies over $q$ or over $q'$; and a $\mathbb{Z}$-submodule $\Lambda$ that is a maximal order. Let $\bar F$ be a field, essentially of finite type and a curve over $\bar{\mathbb{Q}} =$ `AlgebraicClosure ℚ` in the sense of `IsCurveOver`. Let $\pi_X : X \to \operatorname{Spec} \mathbb{Z}[1/D]$ be a scheme over the base, $\bar s$ a $\bar{\mathbb{Q}}$-point of the base, and `pt` an assignment sending a fake elliptic curve with level-$N$ structure $E$ over a commutative ring $S$ together with an $S$-point $s$ of the base to a morphism $\operatorname{Spec} S \to X$ over $s$; it is assumed invariant under `FakeEllipticCurve.Iso`, compatible with pullback along ring maps over the base, and, over algebraically closed fields, surjective onto points over $s$ and injective up to isomorphism. Let $\mathfrak{M}$ be a curve model of $\bar F$ over $\bar{\mathbb{Q}}$ together with an isomorphism $e_{\mathfrak{M}} : \mathfrak{M}.C \to X \times_{\mathbb{Z}[1/D]} \bar{\mathbb{Q}}$ whose composite with the second projection is $\mathfrak{M}$'s structure map; let `gal` be an action of $\operatorname{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})$ by $\bar{\mathbb{Q}}$-semilinear automorphisms of $\bar F$, $\mathbb{T}$ a `HeckeTower.TowerData q q'` over $\bar F$ (fields $\mathbb{T}.F_\ell$ indexed by primes $\ell \notin \{q,q'\}$, each a curve over $\bar{\mathbb{Q}}$ essentially of finite type, with finite integral $\bar{\mathbb{Q}}$-algebra maps $\mathbb{T}.\varphi(\ell,i) : \bar F \to \mathbb{T}.F_\ell$), `galT`, $W$, `WT` the accompanying semilinear data, and `tw` a `ModuliTowerWitnessD` datum for all of these. Fix such an $\ell$. Let $\pi_Y : Y \to \operatorname{Spec} \bar{\mathbb{Q}}$ be integral, separated and smooth of relative dimension $1$, and `ptT` an assignment making $Y$ a coarse moduli space (`IsCoarseModuliT`) for fake elliptic curves with level-$N$ and extra level-$\ell$ structure; let $d_0, d_1 : Y \to X$ satisfy that $d_0$ composed after the $Y$-point of $u$ is the $X$-point of the underlying level-$N$ object of $u$, and $d_1$ composed after the $Y$-point of $u$ is the $X$-point of any $d$ receiving a level-$\ell$ isogeny from $u$. Finally let $F_Y$ be a field, a curve over $\bar{\mathbb{Q}}$ essentially of finite type, $\mathfrak{M}_Y$ a curve model of $F_Y$ with an isomorphism $e_Y : \mathfrak{M}_Y.C \to Y$ over $\bar{\mathbb{Q}}$, and $\psi_0,\psi_1 : \bar F \to F_Y$ integral $\bar{\mathbb{Q}}$-algebra maps such that for every place $R'$ of $F_Y$ over $\bar{\mathbb{Q}}$ the $\bar{\mathbb{Q}}$-point of $\mathfrak{M}.C$ attached to the restriction of $R'$ along $\psi_i$, followed by $e_{\mathfrak{M}}$ and the projection to $X$, equals the point attached to $R'$, followed by $e_Y$ and $d_i$, for $i = 0,1$. The conclusion is that there is a $\bar{\mathbb{Q}}$-algebra isomorphism $\iota : \mathbb{T}.F_\ell \to F_Y$ with $\iota \circ \mathbb{T}.\varphi(\ell,0) = \psi_0$ and $\iota \circ \mathbb{T}.\varphi(\ell,1) = \psi_1$.
--
--   This is the identification of the level-$(N;\ell)$ field of the quaternionic Hecke tower with the function field of the coarse moduli curve of pairs, compatibly with both degeneracy legs; the hypotheses on $\psi_0,\psi_1$ say that these two maps realise the degeneracy morphisms $d_0,d_1$ on geometric points. It is the analytic core of the construction of the curve model at level $(N;\ell)$, and is used by [`CerednikDrinfeld.QM.ModuliTowerWitnessD.exists_curveModel_level_of_pt_pullback_of_two_mul_dvd_of_squarefree`](thm.html#CerednikDrinfeld.QM.ModuliTowerWitnessD.exists_curveModel_level_of_pt_pullback_of_two_mul_dvd_of_squarefree), which transports $\mathfrak{M}_Y$ along $\iota$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_exists_algEquiv_level_comp_phi_eq_of_pt_pullback_of_two_mul_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMModuliTowerD
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
open AlgebraicCurve

theorem CerednikDrinfeld.QM.ModuliTowerWitnessD.exists_algEquiv_level_comp_phi_eq_of_pt_pullback_of_two_mul_dvd
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) (hD : 2 * N * q * q' ∣ D)

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (E E' : FakeEllipticCurve Λ N S), FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (x : SchemeHomOver s πX), ∃ E : FakeEllipticCurve Λ N k, pt k s E = x)
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')

    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) [CategoryTheory.IsIso e𝔐]
    (he𝔐 : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)
    (gal : ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (𝕋 : HeckeTower.TowerData q q' Fbar)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (tw : ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT)
    (ℓ : HeckeTower.AwayPrime q q')

    (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) [IsIntegral Y] [IsSeparated πY]
    (hYsm : SmoothOfRelativeDimension 1 πY)
    (ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))),
      FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S → SchemeHomOver s πY)
    (hY : IsCoarseModuliT Λ N (ℓ.1 : ℕ) Y πY ptT)
    (d₀ d₁ : Y ⟶ X)
    (hd₀ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S), (ptT S s u).1 ≫ d₀ = (pt S (s ≫ sbar) u.1).1)
    (hd₁ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S) (d : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsLevelIsogeny (ℓ.1 : ℕ) u d → (ptT S s u).1 ≫ d₁ = (pt S (s ≫ sbar) d).1)

    (FY : Type) [Field FY] [Algebra (AlgebraicClosure ℚ) FY]
    [IsCurveOver (AlgebraicClosure ℚ) FY] [Algebra.EssFiniteType (AlgebraicClosure ℚ) FY]
    (𝔐Y : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) FY) (eY : 𝔐Y.C ⟶ Y) [IsIso eY] (heY : eY ≫ πY = 𝔐Y.toBase)
    (ψ₀ ψ₁ : Fbar →ₐ[AlgebraicClosure ℚ] FY) (hψ₀ : ψ₀.toRingHom.IsIntegral) (hψ₁ : ψ₁.toRingHom.IsIntegral)
    (hψpt₀ : ∀ R' : Place (AlgebraicClosure ℚ) FY,
      (𝔐.pointEquivPlace.symm (R'.restrictAlong ψ₀ hψ₀)).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar =
        (𝔐Y.pointEquivPlace.symm R').1 ≫ eY ≫ d₀)
    (hψpt₁ : ∀ R' : Place (AlgebraicClosure ℚ) FY,
      (𝔐.pointEquivPlace.symm (R'.restrictAlong ψ₁ hψ₁)).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar =
        (𝔐Y.pointEquivPlace.symm R').1 ≫ eY ≫ d₁) :
    ∃ ι : 𝕋.F ℓ ≃ₐ[AlgebraicClosure ℚ] FY,
      (ι : 𝕋.F ℓ →ₐ[AlgebraicClosure ℚ] FY).comp (𝕋.φ (ℓ, 0)) = ψ₀ ∧
      (ι : 𝕋.F ℓ →ₐ[AlgebraicClosure ℚ] FY).comp (𝕋.φ (ℓ, 1)) = ψ₁ := by sorry
