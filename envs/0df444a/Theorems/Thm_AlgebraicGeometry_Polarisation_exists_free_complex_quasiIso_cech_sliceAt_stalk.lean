-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_free_complex_quasiIso_cech_sliceAt_stalk
-- name    : AlgebraicGeometry.Polarisation.exists_free_complex_quasiIso_cech_sliceAt_stalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/99d5034f-da1d-5214-87cd-2ebd9586a866
-- title:
--   Free local model of the Mumford-slice Čech complex at a stalk
-- statement:
--   Let $K$ be an algebraically closed field and $f : A \to \operatorname{Spec} K$ a morphism of schemes equipped with a relative group law $L$ (functorial multiplication, unit and inverse on $T$-points over $\operatorname{Spec} K$, natural in $T$) and with the bundle of properties `AbelianSchemePropertyBundle` (smoothness, properness, connected fibres, existence of a relative group law), $f$ being smooth of relative dimension $g$; let $M$ and $N$ be invertible $A$-modules, i.e. modules admitting, near every point, a trivialisation of the restriction; let $\mathcal K$ be a finite linearly ordered affine open cover of $A$ with exactly $g+1$ charts, and $y$ a point of $A$. Put $R = \mathcal O_{A,y}$, let $b_R : \operatorname{Spec} R \to A$ be the canonical morphism from the stalk, $t_R = f \circ b_R$, so that $b_R$ is a point $x_R$ of $A$ over $t_R$; let $\pi$ be the second projection $A \times_{\operatorname{Spec} K} \operatorname{Spec} R \to \operatorname{Spec} R$, and let $F_R$ be the pullback along the slice morphism $(\mathrm{pr}_1, b_R \circ \mathrm{pr}_2) : A\times_K \operatorname{Spec} R \to A \times_K A$ of the Mumford bundle $m^*M \otimes (\mathrm{pr}_1^*M^\vee \otimes \mathrm{pr}_2^*M^\vee)$ tensored with $\mathrm{pr}_2^*N$. Let $\mathcal K_R$ be the preimage cover of $\mathcal K$ under $\mathrm{pr}_1$, and $G$ the presheaf of $R$-modules $U \mapsto \Gamma(F_R, U)$ with its restriction maps. The assertion is the existence of finite free $R$-modules $K^i$ with $R$-linear differentials $\delta^i : K^i \to K^{i+1}$ satisfying $\delta^{i+1}\circ\delta^i = 0$ and $K^i = 0$ for $i > g$, of a map of complexes $\varphi^i : K^i \to \check C^i(\mathcal K_R, G)$ into the ordered Čech cochains (families of sections of $F_R$ over the intersections $\bigcap_j U_{s(j)}$ indexed by strictly increasing $s : \{0,\dots,i\} \to \mathcal K_R.\iota$), and, for every commutative $R$-algebra $B$, of $B$-linear maps $\Theta_B^i : B \otimes_R K^i \to \check C^i(\mathcal K_B, F_B)$ for the base change $\pi_B$ of $\pi$ along $\operatorname{Spec} B \to \operatorname{Spec} R$, the pullback $F_B$ of $F_R$ and the base-changed cover, such that: $\ker \delta^0 \cong \check H^0(\mathcal K_R, G)$ and $\ker\delta^{i+1}/\operatorname{im}\delta^i \cong \check H^{i+1}(\mathcal K_R, G)$ $R$-linearly for all $i$; and such that for every $B$ the maps $\Theta_B$ commute with the differentials, are given on pure tensors by $\Theta_B^i(a \otimes k)(s) = a \cdot$ the restriction to the base-changed intersection of the image of $\varphi^i(k)(s)$ under the unit of the pullback– pushforward adjunction, and are a quasi-isomorphism expressed elementwise: a base-changed $0$-cocycle killed by $\Theta_B^0$ vanishes, every $0$-cocycle of $\check C^\bullet(\mathcal K_B, F_B)$ is $\Theta_B^0$ of a cocycle, an $(i+1)$-cocycle of $B \otimes_R K^\bullet$ whose image is a coboundary lies in the image of $(\delta^i)_B$, and every $(i+1)$-cocycle of $\check C^\bullet(\mathcal K_B, F_B)$ agrees modulo coboundaries with the image of some cocycle.
--
--   This is the local model, at the stalk $\mathcal O_{A,y}$, for the cohomology of the Mumford bundle twisted by $\mathrm{pr}_2^*N$ along the section of $A$ determined by $y$: a perfect complex of finite free $R$-modules computing the ordered Čech cohomology of the slice and doing so compatibly with arbitrary base change $R \to B$. It is the input to the seesaw argument for polarisations, being cited by [`AlgebraicGeometry.Polarisation.exists_free_complex_cech_sliceAt_stalk_and_seesaw`](thm.html#AlgebraicGeometry.Polarisation.exists_free_complex_cech_sliceAt_stalk_and_seesaw); freeness, rather than mere projectivity as in the general construction, comes from $R$ being local.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_free_complex_quasiIso_cech_sliceAt_stalk.lean

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

theorem AlgebraicGeometry.Polarisation.exists_free_complex_quasiIso_cech_sliceAt_stalk
    (K : Type) [Field K] [IsAlgClosed K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) (N : A.Modules) (hN : Scheme.Modules.IsInvertible N)
    (𝒦 : A.OrderedAffineCover) (h𝒦 : Fintype.card 𝒦.ι = g + 1) (y : A) :
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
    ∃ (Kc : ℕ → Type) (_ : ∀ i, AddCommGroup (Kc i)) (_ : ∀ i, Module R (Kc i))
      (_ : ∀ i, Module.Finite R (Kc i)) (_ : ∀ i, Module.Free R (Kc i))
      (δ : ∀ i, Kc i →ₗ[R] Kc (i + 1)) (_ : ∀ i, δ (i + 1) ∘ₗ δ i = 0) (_ : ∀ i, g < i → Subsingleton (Kc i))
      (φ : ∀ i, Kc i →ₗ[R] (OModulePresheaf.ofModules π FR).cochain 𝒦R i)
      (_ : ∀ i, (OModulePresheaf.ofModules π FR).d 𝒦R i ∘ₗ φ i = φ (i + 1) ∘ₗ δ i)
      (Θ : ∀ (B : Type) [CommRing B] [Algebra R B] (i : ℕ), B ⊗[R] Kc i →ₗ[B]
        (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R B))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).cochain (𝒦R.baseChange π B) i),
      (Nonempty (LinearMap.ker (δ 0) ≃ₗ[R] G.H0 𝒦R) ∧
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
                  (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R B))).obj FR)).d (𝒦R.baseChange π B) i)) := by sorry
