-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_finrank_ker_baseChange_residue_eq_one_of_quasiIso_cech_sliceAt_stalk_of_forall
-- name    : AlgebraicGeometry.Polarisation.finrank_ker_baseChange_residue_eq_one_of_quasiIso_cech_sliceAt_stalk_of_forall
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/728a2f6d-5d7d-5137-b79e-8177d877750c
-- title:
--   At stabiliser points the local Čech model has h⁰=1
-- statement:
--   Let $K$ be an algebraically closed field, $f : A \to \operatorname{Spec} K$ a morphism of schemes, and $L$ a relative group law on $f$: a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $K$, assumed commutative. Assume the bundle `AbelianSchemePropertyBundle K f`, i.e. $f$ is smooth, proper, has connected fibres and admits a relative group law, and that $f$ is smooth of relative dimension $g$. Let $M$ be an invertible module on $A$, and let $\kappa : KM \to A$ be a closed immersion with $\kappa$ followed by $f$ finite, which represents the stabiliser of $M$ in the sense that for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} K$ and every $R$-point $x$ of $A$ over $t$, the point $x$ factors through $\kappa$ if and only if `L.IsInStabilizer M t x` holds, that is, the pullback of $M$ along translation by $x$ and the pullback of $M$ along the first projection of $A \times_K \operatorname{Spec} R$ are isomorphic locally on $\operatorname{Spec} R$. Let $N$ be a second invertible module and $\mathcal{K}$ an ordered affine cover of $A$ (finitely many affine opens indexed by a linearly ordered type, covering $A$) with exactly $g+1$ members, and let $y$ be a point of $A$ lying in the image of $\kappa$. Put $R = \mathcal{O}_{A,y}$, let $b_R : \operatorname{Spec} R \to A$ be the canonical morphism from the stalk, $t_R = b_R$ followed by $f$, $x_R$ the resulting $R$-point of $A$, and $\pi$ the projection $A \times_K \operatorname{Spec} R \to \operatorname{Spec} R$; let $F_R$ be the pullback along `sliceAt f x_R` of the Mumford bundle $\Lambda(M) = m^{*}M \otimes (p_1^{*}M^{\vee} \otimes p_2^{*}M^{\vee})$ on $A \times_K A$ tensored with $p_2^{*}N$, and $\mathcal{K}_R$ the cover obtained from $\mathcal{K}$ by pulling back along the first projection; let $G$ be the presheaf of $R$-modules of sections of $F_R$. The assertion is: for every family $K^\bullet$ of finite free $R$-modules with $R$-linear maps $\delta^i : K^i \to K^{i+1}$ satisfying $\delta^{i+1} \circ \delta^i = 0$ and $K^i$ trivial for $i > g$, every chain map $\varphi$ from $(K^\bullet,\delta)$ to the Čech complex of $G$ with respect to $\mathcal{K}_R$, and every family of $B$-linear comparison maps $\Theta_B^i : B \otimes_R K^i \to \check{C}^i$ of the base-changed module over $\operatorname{Spec} B$ with its base-changed cover, indexed by $R$-algebras $B$, if (i) $\ker \delta^0$ is $R$-linearly isomorphic to $\check{H}^0(\mathcal{K}_R, G)$ and $\ker \delta^{i+1}/\operatorname{im} \delta^i$ to $\check{H}^{i+1}(\mathcal{K}_R, G)$ for all $i$, and (ii) for every $R$-algebra $B$ the maps $\Theta_B$ form a chain map over $\delta \otimes B$, are given on pure tensors $a \otimes k$ by $a$ times the restriction of the unit of the pullback–pushforward adjunction applied to $\varphi^i(k)$, and are a quasi-isomorphism in the explicit form: $\Theta_B^0$ is injective on $\ker(\delta^0 \otimes B)$ and maps it onto the $0$-cocycles, $\Theta_B^{i+1}$ carries cocycles to coboundaries only when they already lie in the image of $\delta^i \otimes B$, and every $(i+1)$-cocycle differs from some $\Theta_B^{i+1}x$ with $x$ a cocycle by a coboundary, then $\dim_{R/\mathfrak{m}} \ker(\delta^0 \otimes_R R/\mathfrak{m}) = 1$, where $\mathfrak{m}$ is the maximal ideal of $R$.
--
--   This is the rank-one computation on the closed fibre for the local model at a point of the stabiliser subscheme: any finite free complex over the local ring $\mathcal{O}_{A,y}$ whose base changes compute Čech cohomology of the slice of $\Lambda(M) \otimes p_2^{*}N$ must have $h^0 = 1$ after reduction modulo the maximal ideal, because the slice becomes trivial there and $A$ has $h^0(\mathcal{O}_A) = 1$. It transfers `finrank_H0_baseChange_residue_sliceAt_stalk_eq_one` to an arbitrary such complex, and is used in the construction of a free Čech model together with the seesaw input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_finrank_ker_baseChange_residue_eq_one_of_quasiIso_cech_sliceAt_stalk_of_forall.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

open TensorProduct in

theorem AlgebraicGeometry.Polarisation.finrank_ker_baseChange_residue_eq_one_of_quasiIso_cech_sliceAt_stalk_of_forall
    (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    {KM : Scheme.{0}} (κ : KM ⟶ A) (hκ : IsClosedImmersion κ) (hfin : IsFinite (κ ≫ f))
    (hK : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f),
      (∃ x₀ : Spec (CommRingCat.of R) ⟶ KM, x₀ ≫ κ = x.1) ↔ L.IsInStabilizer M t x)
    (N : A.Modules) (hN : Scheme.Modules.IsInvertible N)
    (𝒦 : A.OrderedAffineCover) (h𝒦 : Fintype.card 𝒦.ι = g + 1) (y : A) (hy : y ∈ Set.range κ.base) :
    letI R : Type := ↥(A.presheaf.stalk y)
    letI bR : Spec (CommRingCat.of R) ⟶ A := A.fromSpecStalk y
    letI tR : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K) := bR ≫ f
    letI xR : SchemeHomOver tR f := ⟨bR, rfl⟩
    letI π : pullback f tR ⟶ Spec (CommRingCat.of R) := pullback.snd f tR
    letI FR : (pullback f tR).Modules :=
      (Scheme.Modules.pullback (sliceAt f xR)).obj
        (mumfordBundle f L M ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj N)
    letI _ : IsAffineHom (pullback.fst f tR) := MorphismProperty.pullback_fst _ _ inferInstance
    letI 𝒦R : (pullback f tR).OrderedAffineCover := 𝒦.comap (pullback.fst f tR)
    letI G := OModulePresheaf.ofModules π FR
        ∀ (Kc : ℕ → Type) [∀ i, AddCommGroup (Kc i)] [∀ i, Module R (Kc i)]
        [∀ i, Module.Finite R (Kc i)] [∀ i, Module.Free R (Kc i)]
        (δ : ∀ i, Kc i →ₗ[R] Kc (i + 1)) (_ : ∀ i, δ (i + 1) ∘ₗ δ i = 0) (_ : ∀ i, g < i → Subsingleton (Kc i))
        (φ : ∀ i, Kc i →ₗ[R] (OModulePresheaf.ofModules π FR).cochain 𝒦R i)
        (_ : ∀ i, (OModulePresheaf.ofModules π FR).d 𝒦R i ∘ₗ φ i = φ (i + 1) ∘ₗ δ i)
        (Θ : ∀ (B : Type) [CommRing B] [Algebra R B] (i : ℕ), B ⊗[R] Kc i →ₗ[B]
          (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).cochain (𝒦R.baseChange π B) i),
        (((Nonempty (LinearMap.ker (δ 0) ≃ₗ[R] G.H0 𝒦R) ∧
          ∀ i : ℕ, Nonempty
            ((LinearMap.ker (δ (i + 1)) ⧸ (LinearMap.range (δ i)).comap (LinearMap.ker (δ (i + 1))).subtype) ≃ₗ[R]
              G.HSucc 𝒦R i)) ∧
        ∀ (B : Type) [CommRing B] [Algebra R B],
          (∀ i : ℕ, Θ B (i + 1) ∘ₗ (δ i).baseChange B
            = (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
                ((Scheme.Modules.pullback
                  (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).d (𝒦R.baseChange π B) i
              ∘ₗ Θ B i) ∧
          (∀ (i : ℕ) (a : B) (k : Kc i) (s : 𝒦R.Idx i),
            Θ B i (a ⊗ₜ[R] k) s
              = a • (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
                  ((Scheme.Modules.pullback
                    (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).res
                  (𝒦R.baseChange_inter_le π B s)
                  ((((Scheme.Modules.pullbackPushforwardAdjunction
                    (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).unit.app FR).app
                    (𝒦R.inter s)).hom (φ i k s))) ∧
          (∀ x : B ⊗[R] Kc 0, (δ 0).baseChange B x = 0 → Θ B 0 x = 0 → x = 0) ∧
          (∀ y : (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
              ((Scheme.Modules.pullback
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).cochain (𝒦R.baseChange π B) 0,
            (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
              ((Scheme.Modules.pullback
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).d (𝒦R.baseChange π B) 0 y = 0 →
            ∃ x : B ⊗[R] Kc 0, (δ 0).baseChange B x = 0 ∧ Θ B 0 x = y) ∧
          (∀ (i : ℕ) (x : B ⊗[R] Kc (i + 1)), (δ (i + 1)).baseChange B x = 0 →
            Θ B (i + 1) x ∈ LinearMap.range
              ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
                ((Scheme.Modules.pullback
                  (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).d (𝒦R.baseChange π B) i) →
            x ∈ LinearMap.range ((δ i).baseChange B)) ∧
          (∀ (i : ℕ) (y : (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
              ((Scheme.Modules.pullback
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).cochain (𝒦R.baseChange π B) (i + 1)),
            (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
              ((Scheme.Modules.pullback
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).d (𝒦R.baseChange π B) (i + 1) y = 0 →
            ∃ x : B ⊗[R] Kc (i + 1), (δ (i + 1)).baseChange B x = 0 ∧
              Θ B (i + 1) x - y ∈ LinearMap.range
                ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
                  ((Scheme.Modules.pullback
                    (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).d (𝒦R.baseChange π B) i)))) →
      Module.finrank (R ⧸ IsLocalRing.maximalIdeal R)
        (LinearMap.ker ((δ 0).baseChange (R ⧸ IsLocalRing.maximalIdeal R))) = 1 := by sorry
