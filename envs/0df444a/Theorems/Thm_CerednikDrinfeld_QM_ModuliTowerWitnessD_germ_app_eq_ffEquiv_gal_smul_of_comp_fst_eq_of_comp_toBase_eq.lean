-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_germ_app_eq_ffEquiv_gal_smul_of_comp_fst_eq_of_comp_toBase_eq
-- name    : CerednikDrinfeld.QM.ModuliTowerWitnessD.germ_app_eq_ffEquiv_gal_smul_of_comp_fst_eq_of_comp_toBase_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/b0fcd60e-eeba-5538-aafd-cf431cce6e33
-- title:
--   Pullback along a σ-twist acts as gal σ
-- statement:
--   Fix natural numbers $N$, $D$ and primes $q,q'$, rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, and a field $\bar F$ over $\overline{\mathbb{Q}}=\mathrm{AlgebraicClosure}\,\mathbb{Q}$ which is a curve over $\overline{\mathbb{Q}}$ in the project's sense (principal divisors, finite residue extensions at all places, and $\Omega_{\bar F/\overline{\mathbb{Q}}}$ free of rank one) and essentially of finite type. The data are: a scheme $X$ with a morphism $\pi_X$ to $\operatorname{Spec}\mathbb{Z}[1/D]$ (the localisation away from $D$), a point $\bar s:\operatorname{Spec}\overline{\mathbb{Q}}\to\operatorname{Spec}\mathbb{Z}[1/D]$; an assignment `pt` sending a commutative ring $S$, a morphism $s:\operatorname{Spec}S\to\operatorname{Spec}\mathbb{Z}[1/D]$ and a fake elliptic curve over $S$ (an abelian scheme of relative fibre dimension $2$ with $\Lambda$-action subject to trace conditions and level-$N$ data) to a morphism $\operatorname{Spec}S\to X$ over $\pi_X$, together with the hypotheses `pt_iso` that `pt` is invariant under isomorphism of fake elliptic curves and `pt_pullback` that it is compatible with base change along ring maps $\varphi:S\to S'$ commuting with the structure morphisms, for $\varphi$-pullback pairs $E,E'$; a curve model $\mathfrak{M}$ over $\overline{\mathbb{Q}}$ with function field identified with $\bar F$ by $\mathfrak{M}.\mathrm{ffEquiv}$ (so $\mathfrak{M}.C$ is integral, proper and smooth of relative dimension $1$ over $\operatorname{Spec}\overline{\mathbb{Q}}$ via $\mathfrak{M}.\mathrm{toBase}$, with places matched to closed points); an isomorphism $e_{\mathfrak{M}}:\mathfrak{M}.C\to X\times_{\operatorname{Spec}\mathbb{Z}[1/D]}\operatorname{Spec}\overline{\mathbb{Q}}$ with $e_{\mathfrak{M}}$ followed by the second projection equal to $\mathfrak{M}.\mathrm{toBase}$; a homomorphism $\mathrm{gal}$ from $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ to the group of semilinear automorphisms of $\bar F$ (pairs of ring automorphisms of $\bar F$ and of $\overline{\mathbb{Q}}$ compatible with the structure map); tower data $\mathbb{T}$ for the primes $q,q'$ over $\bar F$, semilinear Galois actions $\mathrm{galT}$ on each tower field, pairs $W$ and $W_T$ of semilinear automorphisms; and a witness $tw$ of the predicate `ModuliTowerWitnessD` for all of these. Let $\sigma$ be an automorphism of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ and let $g:\mathfrak{M}.C\to\mathfrak{M}.C$ satisfy: $g$ followed by $e_{\mathfrak{M}}$ followed by the first projection equals $e_{\mathfrak{M}}$ followed by the first projection, and $g$ followed by $\mathfrak{M}.\mathrm{toBase}$ equals $\mathfrak{M}.\mathrm{toBase}$ followed by $\operatorname{Spec}\sigma$. Then for every $x\in\bar F$, every open $U\subseteq\mathfrak{M}.C$ containing the generic point whose preimage $g^{-1}U$ also contains the generic point, and every section $sec$ over $U$ whose germ at the generic point is $\mathfrak{M}.\mathrm{ffEquiv}(x)$, the germ at the generic point of $(g.\mathrm{app}\,U)(sec)$ over $g^{-1}U$ equals $\mathfrak{M}.\mathrm{ffEquiv}(\mathrm{gal}(\sigma)\cdot x)$.
--
--   This identifies the action of a $\sigma$-semilinear self-map $g$ of the canonical model $\mathfrak{M}.C$ on rational functions: pulling back along $g$ corresponds, under the identification of $\bar F$ with the function field, to the semilinear automorphism $\mathrm{gal}(\sigma)$ prescribed by the moduli-tower witness. It is used in the germ-decomposition statements at the two distinguished places of the Čerednik–Drinfeld comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_ModuliTowerWitnessD_germ_app_eq_ffEquiv_gal_smul_of_comp_fst_eq_of_comp_toBase_eq.lean

import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMModuliTowerD

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.ModuliTowerWitnessD.germ_app_eq_ffEquiv_gal_smul_of_comp_fst_eq_of_comp_toBase_eq
    {N q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (D : ℕ)
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
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
    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) [CategoryTheory.IsIso e𝔐]
    (he𝔐 : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)
    (gal : ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (𝕋 : HeckeTower.TowerData q q' Fbar)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (tw : ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))

    (g : 𝔐.C ⟶ 𝔐.C)
    (hg₁ : g ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar = e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar)
    (hg₂ : g ≫ 𝔐.toBase = 𝔐.toBase ≫ Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)))
    (x : Fbar) (U : 𝔐.C.Opens) (hU : (genericPoint (𝔐.C : Scheme.{0})) ∈ U)
    (hU' : (genericPoint (𝔐.C : Scheme.{0})) ∈ g ⁻¹ᵁ U) (sec : 𝔐.C.presheaf.obj (Opposite.op U))
    (hsec : (𝔐.C.presheaf.germ U (genericPoint (𝔐.C : Scheme.{0})) hU).hom sec = 𝔐.ffEquiv x) :
    (𝔐.C.presheaf.germ (g ⁻¹ᵁ U) (genericPoint (𝔐.C : Scheme.{0})) hU').hom ((g.app U).hom sec) = 𝔐.ffEquiv (gal σ • x) := by sorry
