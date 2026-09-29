-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isClosedImmersion_lfp_chart_iff_of_descent
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_isClosedImmersion_lfp_chart_iff_of_descent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/810bced4-39c3-5f11-a6c9-fc3e9a809577
-- title:
--   Descent of the triviality locus to an affine chart
-- statement:
--   Let $R$ be a commutative ring, let $f : A \to \operatorname{Spec} R$ be a morphism of schemes carrying a relative group law $L$ (functorial multiplication, unit and inverse on $T$-points over $\operatorname{Spec} R$, natural in $T$) and satisfying the conjunction `AbelianSchemePropertyBundle` (smooth, proper, connected fibres, a relative group law exists), let $g : X \to \operatorname{Spec} R$ be a morphism and let $M$ be a rigidified line bundle for $f$, $g$ and the unit section $L.\mathrm{one}$: an invertible module on $A \times_{\operatorname{Spec} R} X$ with a trivialisation along the rigidifying section. Let $U$ be an affine open of $X$. Suppose given a noetherian commutative ring $R_0$, a ring homomorphism $\varphi : R_0 \to R$, data $f_0 : A_0 \to \operatorname{Spec} R_0$ with relative group law $L_0$ and the same bundle of properties, a morphism $g_0 : X_0 \to \operatorname{Spec} R_0$ locally of finite type, a rigidified line bundle $M_0$ for $f_0$, $g_0$ and $L_0.\mathrm{one}$, together with comparison morphisms $a : A \to A_0$ and $u : U \to X_0$ whose squares over $\operatorname{Spec}\varphi$ are cartesian, the compatibility that $a$ carries $L$-multiplication of $T$-points to $L_0$-multiplication of their images, and an isomorphism between the underlying module of $M$ restricted to $A \times_{\operatorname{Spec} R} U$ and the pullback of the module of $M_0$ along the induced map to $A_0 \times_{\operatorname{Spec} R_0} X_0$. Suppose finally that $\iota_0 : Z_0 \to X_0$ is a closed immersion representing triviality for $M_0$: for every scheme $T$, every $t : T \to \operatorname{Spec} R_0$ and every $\psi : T \to X_0$ over $t$, the module of $M_0$ pulled back along $\psi$ is isomorphic to the structure sheaf of $A_0 \times_{\operatorname{Spec} R_0} T$ exactly when $\psi$ factors through $\iota_0$. Then there exist a scheme $Z_U$ and a morphism $\iota_U : Z_U \to U$ which is a closed immersion and locally of finite presentation, such that for every scheme $T$, every $t : T \to \operatorname{Spec} R$ and every $\psi_U : T \to U$ with $\psi_U$ followed by $U \hookrightarrow X$ and then $g$ equal to $t$, the module of $M$ pulled back along $\psi_U$ followed by $U \hookrightarrow X$ is isomorphic to the structure sheaf of $A \times_{\operatorname{Spec} R} T$ exactly when $\psi_U$ factors through $\iota_U$.
--
--   This is the base-change step for the locus where a rigidified line bundle on an abelian scheme becomes trivial: a representing closed subscheme over the noetherian ring $R_0$ is transported, by pulling back along the cartesian comparison maps, to a closed subscheme of the affine chart $U$ over $R$, the finite presentation coming from noetherianity downstairs. It is used in the construction of the see-saw triviality locus over a general base, where the charts obtained here are glued over an affine cover of $X$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isClosedImmersion_lfp_chart_iff_of_descent.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_isClosedImmersion_lfp_chart_iff_of_descent
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hA : AbelianSchemePropertyBundle R f)
    {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle f (L.one (𝟙 (Spec (CommRingCat.of R)))) g) (U : X.affineOpens)
    (R₀ : Type) [CommRing R₀] [IsNoetherianRing R₀] (φ : R₀ →+* R)
    (A₀ : Scheme.{0}) (f₀ : A₀ ⟶ Spec (CommRingCat.of R₀)) (L₀ : RelativeGroupLaw R₀ f₀) (hA₀ : AbelianSchemePropertyBundle R₀ f₀)
    (X₀ : Scheme.{0}) (g₀ : X₀ ⟶ Spec (CommRingCat.of R₀)) [LocallyOfFiniteType g₀]
    (M₀ : RigidifiedLineBundle f₀ (L₀.one (𝟙 (Spec (CommRingCat.of R₀)))) g₀)
    (a : A ⟶ A₀) (ha : IsPullback a f f₀ (Spec.map (CommRingCat.ofHom φ)))
    (u : ((U : X.Opens) : Scheme.{0}) ⟶ X₀) (hu : IsPullback u ((U : X.Opens).ι ≫ g) g₀ (Spec.map (CommRingCat.ofHom φ)))
    (hLa : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ a = (L₀.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1)
    (hM : Nonempty ((M.pullbackAlong (⟨(U : X.Opens).ι, rfl⟩ : SchemeHomOver ((U : X.Opens).ι ≫ g) g)).L ≅
      (Scheme.Modules.pullback
        (pullback.map f ((U : X.Opens).ι ≫ g) f₀ g₀ a u (Spec.map (CommRingCat.ofHom φ)) ha.w.symm hu.w.symm)).obj M₀.L))
    (Z₀ : Scheme.{0}) (ι₀ : Z₀ ⟶ X₀) (hι₀ : IsClosedImmersion ι₀)
    (hZ₀ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R₀)) (ψ : SchemeHomOver t g₀),
        Nonempty ((M₀.pullbackAlong ψ).L ≅
            (RigidifiedLineBundle.unit (c := f₀) (ε := L₀.one (𝟙 (Spec (CommRingCat.of R₀)))) t).L) ↔
          ∃ ψ₀ : T ⟶ Z₀, ψ₀ ≫ ι₀ = ψ.1) :
    ∃ (ZU : Scheme.{0}) (ιU : ZU ⟶ ((U : X.Opens) : Scheme.{0})),
        IsClosedImmersion ιU ∧ LocallyOfFinitePresentation ιU ∧
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (ψU : T ⟶ ((U : X.Opens) : Scheme.{0}))
          (hψ : (ψU ≫ (U : X.Opens).ι) ≫ g = t),
          (Nonempty ((M.pullbackAlong (⟨ψU ≫ (U : X.Opens).ι, hψ⟩ : SchemeHomOver t g)).L ≅
              (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) t).L) ↔
            ∃ ψ₀ : T ⟶ ZU, ψ₀ ≫ ιU = ψU) := by sorry
