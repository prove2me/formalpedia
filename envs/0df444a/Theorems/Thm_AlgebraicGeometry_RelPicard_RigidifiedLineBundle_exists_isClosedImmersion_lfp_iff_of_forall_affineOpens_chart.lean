-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isClosedImmersion_lfp_iff_of_forall_affineOpens_chart
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_isClosedImmersion_lfp_iff_of_forall_affineOpens_chart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/66d468bd-dcc8-57e5-b465-6bcd37db5fc5
-- title:
--   Gluing chart-local triviality loci, with local finite presentation
-- statement:
--   Let $R$ be a commutative ring, let $f\colon A\to\operatorname{Spec}R$ be a morphism of schemes, let $L$ be a relative group law on $f$ (a functorial group structure, natural in the base, on the sets $\{\varphi\colon T\to A \mid \varphi\circ f=t\}$ of $R$-points of $A$), and let $hA$ witness the bundle of properties `AbelianSchemePropertyBundle` for $f$: $f$ is smooth and proper, every fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $g\colon X\to\operatorname{Spec}R$ be a scheme over $R$ and let $M$ be a line bundle on $A\times_{\operatorname{Spec}R}X$, Zariski-locally trivial and rigidified along the section cut out by the unit $L.\mathrm{one}$ of the group law, i.e. an object of `RigidifiedLineBundle`. Assume that for every affine open $U\subseteq X$ there are a scheme $Z_U$ and a morphism $\iota_U\colon Z_U\to U$ which is a closed immersion and locally of finite presentation, such that for every scheme $T$, every $t\colon T\to\operatorname{Spec}R$ and every $\psi_U\colon T\to U$ with $(\psi_U\circ U\hookrightarrow X)\circ g=t$, the pullback of $M$ along $\psi_U$ followed by the inclusion of $U$ has invertible sheaf isomorphic to the structure sheaf of $A\times_{\operatorname{Spec}R}T$ if and only if $\psi_U$ factors through $\iota_U$. The conclusion is that there exist a scheme $Z$ and a morphism $\iota\colon Z\to X$ which is a closed immersion and locally of finite presentation, such that for every $T$, every $t\colon T\to\operatorname{Spec}R$ and every $\psi\colon T\to X$ over $R$, the pullback of $M$ along $\psi$ has trivial underlying line bundle if and only if $\psi$ factors through $\iota$.
--
--   This is the gluing step for the see-saw (triviality) locus of a rigidified line bundle on $A\times_R X$: chart-local closed subschemes representing the locus of triviality glue to a global closed subscheme representing it, and the extra property of being locally of finite presentation is carried along. It feeds the construction of the representing closed subscheme for the triviality locus over a general base, used in the relative Picard formalism for Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isClosedImmersion_lfp_iff_of_forall_affineOpens_chart.lean

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

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_isClosedImmersion_lfp_iff_of_forall_affineOpens_chart
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hA : AbelianSchemePropertyBundle R f)
    {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle f (L.one (𝟙 (Spec (CommRingCat.of R)))) g)
    (hloc : ∀ U : X.affineOpens, ∃ (ZU : Scheme.{0}) (ιU : ZU ⟶ ((U : X.Opens) : Scheme.{0})),
        IsClosedImmersion ιU ∧ LocallyOfFinitePresentation ιU ∧
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (ψU : T ⟶ ((U : X.Opens) : Scheme.{0}))
          (hψ : (ψU ≫ (U : X.Opens).ι) ≫ g = t),
          (Nonempty ((M.pullbackAlong (⟨ψU ≫ (U : X.Opens).ι, hψ⟩ : SchemeHomOver t g)).L ≅
              (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) t).L) ↔
            ∃ ψ₀ : T ⟶ ZU, ψ₀ ≫ ιU = ψU)) :
    ∃ (Z : Scheme.{0}) (ι : Z ⟶ X), IsClosedImmersion ι ∧ LocallyOfFinitePresentation ι ∧
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (ψ : SchemeHomOver t g),
        Nonempty ((M.pullbackAlong ψ).L ≅
            (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) t).L) ↔
          ∃ ψ₀ : T ⟶ Z, ψ₀ ≫ ι = ψ.1 := by sorry
