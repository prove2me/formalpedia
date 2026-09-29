-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_noetherian_descent_affineOpens_of_isPullback_of_isPullback
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_noetherian_descent_affineOpens_of_isPullback_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/411c535e-e2b7-530b-9091-729d52e71a25
-- title:
--   Noetherian descent of a rigidified bundle over an affine chart
-- statement:
--   Let $R$ be a commutative ring, let $f : A \to \operatorname{Spec} R$ be a morphism of schemes carrying a relative group law $L$ (a functorial group structure, with naturality under base change, on the sets of sections $\{\varphi : T \to A \mid \varphi \circ f = t\}$ for $t : T \to \operatorname{Spec} R$) and satisfying `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper with connected fibres and admits some relative group law; let $g : X \to \operatorname{Spec} R$ be locally of finite presentation, let $M$ be a rigidified line bundle for $f$, the unit section $L.\mathrm{one}$ and $g$ — an invertible module on $A \times_{\operatorname{Spec} R} X$ whose pullback along the section determined by the unit is isomorphic to the structure sheaf — and let $U$ be an affine open of $X$. Assume a partial descent to a finitely generated $\mathbb{Z}$-subalgebra $S_1 \subseteq R$ is given: a scheme $A_1$ with $f_1 : A_1 \to \operatorname{Spec} S_1$ carrying a relative group law $L_1$ and satisfying the same smooth-proper-connected bundle of properties, a morphism $a_1 : A \to A_1$ making $f$ the base change of $f_1$ along $\operatorname{Spec} S_1 \to \operatorname{Spec} R$ and intertwining the multiplications of $L$ and $L_1$ on sections; and a quasi-compact, quasi-separated $g_1 : X_1 \to \operatorname{Spec} S_1$ locally of finite type together with $u_1 : U \to X_1$ exhibiting $U \to \operatorname{Spec} R$ as the base change of $g_1$. Then there exist a Noetherian commutative ring $R_0$, a ring homomorphism $\varphi : R_0 \to R$, a scheme $A_0$ with $f_0 : A_0 \to \operatorname{Spec} R_0$ carrying a relative group law $L_0$ and satisfying the same bundle of properties, a morphism $g_0 : X_0 \to \operatorname{Spec} R_0$ locally of finite type, a rigidified line bundle $M_0$ for $f_0$, the unit of $L_0$ and $g_0$, and morphisms $a : A \to A_0$, $u : U \to X_0$ exhibiting $f$ and $U \to \operatorname{Spec} R$ as base changes of $f_0$ and $g_0$ along $\operatorname{Spec} \varphi$, such that $a$ intertwines the multiplications of $L$ and $L_0$ on sections and the restriction of $M$ to $A \times_{\operatorname{Spec} R} U$ (its pullback along the section given by the inclusion $U \hookrightarrow X$) is isomorphic to the pullback of $M_0$ along the induced map $A \times_{\operatorname{Spec} R} U \to A_0 \times_{\operatorname{Spec} R_0} X_0$. No compatibility between $R_0$ and the given $S_1$ is asserted.
--
--   This is the module-theoretic step of Noetherian approximation (EGA IV, §8) for the data used in the relative Picard construction: the descents of the abelian scheme with its group law and of the affine chart are taken as hypotheses, and what is produced in addition is a descent of the rigidified line bundle over a Noetherian base. It is the sole input of [`AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_noetherian_descent_affineOpens`](thm.html#AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_noetherian_descent_affineOpens), whose conclusion it reproduces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_noetherian_descent_affineOpens_of_isPullback_of_isPullback.lean

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

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_noetherian_descent_affineOpens_of_isPullback_of_isPullback
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hA : AbelianSchemePropertyBundle R f)
    {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation g]
    (M : RigidifiedLineBundle f (L.one (𝟙 (Spec (CommRingCat.of R)))) g) (U : X.affineOpens)
    (S₁ : Subalgebra ℤ R) (hS₁ : S₁.FG)
    (A₁ : Scheme.{0}) (f₁ : A₁ ⟶ Spec (CommRingCat.of ↥S₁)) (L₁ : RelativeGroupLaw ↥S₁ f₁) (hA₁ : AbelianSchemePropertyBundle ↥S₁ f₁)
    (a₁ : A ⟶ A₁) (ha₁ : IsPullback a₁ f f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥S₁ R))))
    (hLa₁ : (∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ a₁ = (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥S₁ R)))
        ⟨P.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, Q.2]⟩).1))
    (X₁ : Scheme.{0}) (g₁ : X₁ ⟶ Spec (CommRingCat.of ↥S₁)) [LocallyOfFiniteType g₁] [QuasiCompact g₁] [QuasiSeparated g₁]
    (u₁ : ((U : X.Opens) : Scheme.{0}) ⟶ X₁)
    (hu₁ : IsPullback u₁ ((U : X.Opens).ι ≫ g) g₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥S₁ R)))) :
    ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsNoetherianRing R₀) (φ : R₀ →+* R)
        (A₀ : Scheme.{0}) (f₀ : A₀ ⟶ Spec (CommRingCat.of R₀)) (L₀ : RelativeGroupLaw R₀ f₀) (_ : AbelianSchemePropertyBundle R₀ f₀)
        (X₀ : Scheme.{0}) (g₀ : X₀ ⟶ Spec (CommRingCat.of R₀)) (_ : LocallyOfFiniteType g₀)
        (M₀ : RigidifiedLineBundle f₀ (L₀.one (𝟙 (Spec (CommRingCat.of R₀)))) g₀)
        (a : A ⟶ A₀) (ha : IsPullback a f f₀ (Spec.map (CommRingCat.ofHom φ)))
        (u : ((U : X.Opens) : Scheme.{0}) ⟶ X₀) (hu : IsPullback u ((U : X.Opens).ι ≫ g) g₀ (Spec.map (CommRingCat.ofHom φ))),

        (∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
          (L.mul t P Q).1 ≫ a = (L₀.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
            ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1) ∧

        Nonempty ((M.pullbackAlong (⟨(U : X.Opens).ι, rfl⟩ : SchemeHomOver ((U : X.Opens).ι ≫ g) g)).L ≅
          (Scheme.Modules.pullback
            (pullback.map f ((U : X.Opens).ι ≫ g) f₀ g₀ a u (Spec.map (CommRingCat.ofHom φ)) ha.w.symm hu.w.symm)).obj M₀.L) := by sorry
