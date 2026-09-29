-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isClosedImmersion_iff_of_forall_affineOpens_chart
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_isClosedImmersion_iff_of_forall_affineOpens_chart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/e99d8adf-b8b1-5b6b-9191-32b9e3e37b6c
-- title:
--   Gluing chart-local triviality loci of a rigidified line bundle
-- statement:
--   Fix a commutative ring $R$, a scheme $A$ and a morphism $f\colon A\to\operatorname{Spec}R$, together with a relative group law $L$ on the functor $T\mapsto\{\varphi\colon T\to A\mid \varphi\circ f = t\}$ of points of $f$ over $R$ (functorial multiplication, unit and inverse satisfying the group axioms and compatible with base change) and a bundle of properties `AbelianSchemePropertyBundle R f`, i.e. $f$ is smooth and proper, each fibre of $f$ over a point of $\operatorname{Spec}R$ is connected, and the functor of points of $f$ carries some relative group law. Let $g\colon X\to\operatorname{Spec}R$ be a further scheme over $R$ and let $M$ be a rigidified line bundle for $f$ along the unit section $L.\mathrm{one}(\mathrm{id})$ over $g$: a module $M.L$ on $A\times_{\operatorname{Spec}R}X$ which is locally isomorphic to the unit module, together with a trivialisation of its pullback along the rigidifying section determined by the unit. Assume the chart-local hypothesis: for every affine open $U\subseteq X$ there are a scheme $Z_U$ and a closed immersion $\iota_U\colon Z_U\to U$ such that for every scheme $T$, every $t\colon T\to\operatorname{Spec}R$ and every $\psi_U\colon T\to U$ whose composite with the inclusion of $U$ followed by $g$ equals $t$, the module underlying the pullback of $M$ along $\psi_U$ followed by the inclusion of $U$ is isomorphic to the module underlying the unit rigidified bundle over $t$ if and only if $\psi_U$ factors through $\iota_U$. The conclusion asserts the existence of a scheme $Z$ and a closed immersion $\iota\colon Z\to X$ with the same property globally: for every scheme $T$, every $t\colon T\to\operatorname{Spec}R$ and every $\psi\colon T\to X$ with $\psi\circ g=t$, the pullback of $M$ along $\psi$ has underlying module isomorphic to the unit module on $A\times_{\operatorname{Spec}R}T$ precisely when $\psi$ factors through $\iota$.
--
--   This is the Zariski gluing step for the triviality (see-saw) locus of a rigidified line bundle on $A\times_R X$: closed subschemes of affine charts of $X$ representing the locus where the bundle becomes trivial are patched into a single closed subscheme of $X$ representing the same condition. It feeds the representability statements for the triviality locus, in particular the version over a Noetherian base and the variant formulated for the functor built from it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isClosedImmersion_iff_of_forall_affineOpens_chart.lean

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

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_isClosedImmersion_iff_of_forall_affineOpens_chart
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hA : AbelianSchemePropertyBundle R f)
    {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle f (L.one (𝟙 (Spec (CommRingCat.of R)))) g)
    (hloc : ∀ U : X.affineOpens, ∃ (ZU : Scheme.{0}) (ιU : ZU ⟶ ((U : X.Opens) : Scheme.{0})), IsClosedImmersion ιU ∧
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (ψU : T ⟶ ((U : X.Opens) : Scheme.{0}))
          (hψ : (ψU ≫ (U : X.Opens).ι) ≫ g = t),
          (Nonempty ((M.pullbackAlong (⟨ψU ≫ (U : X.Opens).ι, hψ⟩ : SchemeHomOver t g)).L ≅
              (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) t).L) ↔
            ∃ ψ₀ : T ⟶ ZU, ψ₀ ≫ ιU = ψU)) :
    ∃ (Z : Scheme.{0}) (ι : Z ⟶ X), IsClosedImmersion ι ∧
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (ψ : SchemeHomOver t g),
        Nonempty ((M.pullbackAlong ψ).L ≅
            (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) t).L) ↔
          ∃ ψ₀ : T ⟶ Z, ψ₀ ≫ ι = ψ.1 := by sorry
