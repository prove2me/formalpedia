-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_unitPullback_sub_unitPullback_mem_range_d_of_rosatiCompatible_of_isPicObstructionCocycle_mumfordBundle
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.unitPullback_sub_unitPullback_mem_range_d_of_rosatiCompatible_of_isPicObstructionCocycle_mumfordBundle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/1e5f6414-c391-5b8c-ac49-401d42fd9d63
-- title:
--   Rosati compatibility: two pullbacks of the obstruction cocycle are cohomologous
-- statement:
--   Fix $a,b\in\mathbb{Q}$, a $\mathbb{Z}$-submodule $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$, an arbitrary self-map $\star$ of $\Lambda$ (no involution property is required) and $N\in\mathbb{N}$. Let $B_1$ be a local ring and $B_0$ a $B_1$-algebra with $B_1\to B_0$ surjective, whose kernel $J$ satisfies $J\cdot\mathfrak{m}=0$ (elementwise: $xm=0$ for $x\in J$, $m\in\mathfrak m$) and $J\subseteq\mathfrak{m}$; let $V$ be a finite-dimensional module over $k=\mathrm{ResidueField}\,B_1$ which is also a $B_1$-module compatibly, and $\iota:V\to B_1$ an injective $B_1$-linear map with image exactly $J$. Let $E$, $E_0$, $E_k$ be fake elliptic curves for $(\Lambda,N)$ over $B_1$, $B_0$, $k$, with affine morphisms $g:E_0.A\to E.A$ and $i_k:E_k.A\to E.A$ exhibiting $E_0$, $E_k$ as base changes of $E$ along $B_1\to B_0$ and $B_1\to k$ in the sense of `IsPullbackVia` (pullback square, compatibility with the relative group law and with the $\Lambda$-actions, and lifting of level points), and let $g_{XX}$, $i_{XX}$ be affine morphisms of the fibre squares $E_\bullet.A\times E_\bullet.A\to E.A\times E.A$ commuting with both projections via $g$, resp. $i_k$. Let $\mathcal{L}_0$ be an $\mathcal{O}_{E_0.A}$-module which is Rosati-compatible through $\star$: for every $b\in\Lambda$ the pullbacks of the Mumford bundle $\Lambda(\mathcal{L}_0)=\mathrm{add}^*\mathcal{L}_0\otimes(\mathrm{fst}^*\mathcal{L}_0^\vee\otimes\mathrm{snd}^*\mathcal{L}_0^\vee)$ along $(1,\,\mathrm{act}(b)\circ\mathrm{snd})$ and along $(\mathrm{act}(\star b)\circ\mathrm{fst},\,1)$ are `LocIsoOnBase` over $\mathrm{fst}\circ E_0.f$. Let $\mathcal{W}$ be a finite ordered affine cover of $E.A\times E.A$ and $C:V^\vee\to$ (degree-$2$ cochains of the unit $\mathcal{O}$-module presheaf of $\mathrm{fst}\circ E_k.f$ on $i_{XX}^{-1}\mathcal{W}$) a $k$-linear map which is a Picard obstruction cocycle for $\Lambda(\mathcal{L}_0)$ in the sense of `IsPicObstructionCocycle` (there are a Čech trivialisation of $\Lambda(\mathcal{L}_0)$ on $g_{XX}^{-1}\mathcal{W}$, units $u$, $u'$ on the pairwise intersections with $u$ restricting to the transition functions and $uu'=1$, and on each triple intersection the defect of the cocycle relation from $1$ is a fibre reading of the corresponding component of $C$). Fix $x\in\Lambda$ and a second ordered affine cover $\mathcal{W}'$ of $E.A\times E.A$ together with index maps $\lambda_A,\lambda_B:\mathcal{W}'.\iota\to\mathcal{W}.\iota$ refining $\mathcal{W}$ along $F_1=(\mathrm{fst},\,E.\mathrm{act}(x)\circ\mathrm{snd})$ and $F_2=(E.\mathrm{act}(\star x)\circ\mathrm{fst},\,\mathrm{snd})$, and similarly for the covers $i_{XX}^{-1}\mathcal{W}'$, $i_{XX}^{-1}\mathcal{W}$ and the corresponding morphisms built from $E_k.\mathrm{act}$. Then for every $\xi\in V^\vee$ the difference of the signed Čech pullbacks (`OModulePresheaf.unitPullback`) of $C(\xi)$ along these two morphisms of the special fibre, taken in degree $2$ with the index maps $\lambda_A$ and $\lambda_B$, lies in the image of the Čech differential from degree-$1$ to degree-$2$ cochains of the unit presheaf on $i_{XX}^{-1}\mathcal{W}'$.
--
--   This is the Rosati-compatibility input to the vanishing of the Picard obstruction for lifting a Mumford bundle across a small extension: the two endomorphisms $1\times\iota(x)$ and $\iota(x^\star)\times 1$ of $E.A\times E.A$ exist already over $B_1$ because the chosen lift $E$ carries the $\Lambda$-action, so the naturality of the obstruction class applies to both and Rosati compatibility identifies the two pulled-back bundles over $B_0$, forcing the two pulled-back cocycles to differ by a coboundary. It is used in the two theorems producing an invertible pullback for a Rosati-compatible bundle under a small extension with $\ker\cdot\mathfrak m=0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_unitPullback_sub_unitPullback_mem_range_d_of_rosatiCompatible_of_isPicObstructionCocycle_mumfordBundle.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra
  CerednikDrinfeld CerednikDrinfeld.QM IsLocalRing AlgebraicGeometry.Polarisation AlgebraicGeometry.SmallExtension
open scoped Quaternion TensorProduct

theorem CerednikDrinfeld.QM.FakeEllipticCurve.unitPullback_sub_unitPullback_mem_range_d_of_rosatiCompatible_of_isPicObstructionCocycle_mumfordBundle
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (star : ↥Λ → ↥Λ) {N : ℕ}
    (B₁ B₀ : Type) [CommRing B₁] [IsLocalRing B₁] [CommRing B₀] [Algebra B₁ B₀]
    (hπ : Function.Surjective (algebraMap B₁ B₀))
    (hsmall : ∀ x ∈ RingHom.ker (algebraMap B₁ B₀), ∀ m ∈ maximalIdeal B₁, x * m = 0)
    (hI : RingHom.ker (algebraMap B₁ B₀) ≤ maximalIdeal B₁)
    (V : Type) [AddCommGroup V] [Module (ResidueField B₁) V] [Module.Finite (ResidueField B₁) V]
    [Module B₁ V] [IsScalarTower B₁ (ResidueField B₁) V]
    (ι : V →ₗ[B₁] B₁) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B₁ (RingHom.ker (algebraMap B₁ B₀)))

    (E : FakeEllipticCurve Λ N B₁) (E₀ : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A) [IsAffineHom g]
    (hg : FakeEllipticCurve.IsPullbackVia (algebraMap B₁ B₀) E E₀ g)
    (Ek : FakeEllipticCurve Λ N (ResidueField B₁)) (ik : Ek.A ⟶ E.A) [IsAffineHom ik]
    (hik : FakeEllipticCurve.IsPullbackVia (residue B₁) E Ek ik)

    (gXX : pullback E₀.f E₀.f ⟶ pullback E.f E.f) [IsAffineHom gXX]
    (hg₁ : gXX ≫ pullback.fst E.f E.f = pullback.fst E₀.f E₀.f ≫ g)
    (hg₂ : gXX ≫ pullback.snd E.f E.f = pullback.snd E₀.f E₀.f ≫ g)
    (iXX : pullback Ek.f Ek.f ⟶ pullback E.f E.f) [IsAffineHom iXX]
    (hi₁ : iXX ≫ pullback.fst E.f E.f = pullback.fst Ek.f Ek.f ≫ ik)
    (hi₂ : iXX ≫ pullback.snd E.f E.f = pullback.snd Ek.f Ek.f ≫ ik)

    (𝓛₀ : E₀.A.Modules) (hR₀ : RosatiCompatible E₀.f E₀.L 𝓛₀ E₀.act E₀.act_over star)
    (𝒲 : (pullback E.f E.f).OrderedAffineCover)
    (C : Module.Dual (ResidueField B₁) V →ₗ[ResidueField B₁]
      (OModulePresheaf.unit (pullback.fst Ek.f Ek.f ≫ Ek.f)).cochain (𝒲.comap iXX) 2)
    (hC : IsPicObstructionCocycle V ι (pullback.fst E.f E.f ≫ E.f) (pullback.fst Ek.f Ek.f ≫ Ek.f) iXX gXX 𝒲
      (mumfordBundle E₀.f E₀.L 𝓛₀) C)
    (x : ↥Λ)

    (𝒲' : (pullback E.f E.f).OrderedAffineCover) (lamA lamB : 𝒲'.ι → 𝒲.ι)
    (hA : ∀ w, 𝒲'.U w ≤
      (pullback.lift (pullback.fst E.f E.f) (pullback.snd E.f E.f ≫ E.act x)
        (by rw [Category.assoc, E.act_over]; exact pullback.condition)) ⁻¹ᵁ 𝒲.U (lamA w))
    (hB : ∀ w, 𝒲'.U w ≤
      (pullback.lift (pullback.fst E.f E.f ≫ E.act (star x)) (pullback.snd E.f E.f)
        (by rw [Category.assoc, E.act_over]; exact pullback.condition)) ⁻¹ᵁ 𝒲.U (lamB w))
    (hkA : ∀ w, (𝒲'.comap iXX).U w ≤
      (pullback.lift (pullback.fst Ek.f Ek.f) (pullback.snd Ek.f Ek.f ≫ Ek.act x)
        (by rw [Category.assoc, Ek.act_over]; exact pullback.condition)) ⁻¹ᵁ (𝒲.comap iXX).U (lamA w))
    (hkB : ∀ w, (𝒲'.comap iXX).U w ≤
      (pullback.lift (pullback.fst Ek.f Ek.f ≫ Ek.act (star x)) (pullback.snd Ek.f Ek.f)
        (by rw [Category.assoc, Ek.act_over]; exact pullback.condition)) ⁻¹ᵁ (𝒲.comap iXX).U (lamB w)) :
    ∀ ξ : Module.Dual (ResidueField B₁) V,
      OModulePresheaf.unitPullback (πX := pullback.fst Ek.f Ek.f ≫ Ek.f)
          (pullback.lift (pullback.fst Ek.f Ek.f) (pullback.snd Ek.f Ek.f ≫ Ek.act x)
            (by rw [Category.assoc, Ek.act_over]; exact pullback.condition))
          (𝒲'.comap iXX) (𝒲.comap iXX) lamA hkA 2 (C ξ) -
        OModulePresheaf.unitPullback (πX := pullback.fst Ek.f Ek.f ≫ Ek.f)
          (pullback.lift (pullback.fst Ek.f Ek.f ≫ Ek.act (star x)) (pullback.snd Ek.f Ek.f)
            (by rw [Category.assoc, Ek.act_over]; exact pullback.condition))
          (𝒲'.comap iXX) (𝒲.comap iXX) lamB hkB 2 (C ξ) ∈
      LinearMap.range ((OModulePresheaf.unit (pullback.fst Ek.f Ek.f ≫ Ek.f)).d (𝒲'.comap iXX) 1) := by sorry
