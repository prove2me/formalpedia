-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isClosedImmersion_lfp_chart_iff_affineOpens_of_locallyOfFinitePresentation
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_isClosedImmersion_lfp_chart_iff_affineOpens_of_locallyOfFinitePresentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/fd33767a-1f17-5fa9-9f63-06c05c8b2dbb
-- title:
--   See-saw locus on an affine chart over a general base
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f\colon A\to\operatorname{Spec}R$ a morphism, $L$ a relative group law on $f$ (a group structure, functorial in the base, on the sets $\{\varphi\colon T\to A \mid \varphi\circ f = t\}$ of sections of $f$ over $R$-schemes $t\colon T\to\operatorname{Spec}R$, with multiplication natural in $T$), and let $hA$ assert that $f$ is smooth and proper, that every fibre of $f$ over a point of $\operatorname{Spec}R$ is connected, and that $f$ admits a relative group law. Let $g\colon X\to\operatorname{Spec}R$ be locally of finite presentation, let $M$ be a rigidified line bundle for $f$, $g$ and the unit section $\varepsilon=L.\mathrm{one}(\mathrm{id})$ — that is, an invertible module on $A\times_{\operatorname{Spec}R}X$ together with a trivialisation of its pullback along the section $\mathrm{rigSection}$ cut out by $\varepsilon$ — and let $U$ be an affine open of $X$. Then there exist a scheme $Z_U$ and a morphism $\iota_U\colon Z_U\to U$ (with $U$ viewed as a scheme) such that $\iota_U$ is a closed immersion and locally of finite presentation, and such that for every scheme $T$, every $t\colon T\to\operatorname{Spec}R$ and every $\psi_U\colon T\to U$ with $(\psi_U$ followed by the open immersion $U\to X$ followed by $g)=t$, the underlying module of the pullback of $M$ along the resulting $R$-morphism $T\to X$ is isomorphic to the unit module on $A\times_{\operatorname{Spec}R}T$ if and only if $\psi_U$ factors as $\psi_0$ followed by $\iota_U$ for some $\psi_0\colon T\to Z_U$.
--
--   This is the see-saw (triviality) locus of a rigidified line bundle on an abelian scheme, cut out on a single affine chart of the parameter scheme $X$ and over an arbitrary, not necessarily Noetherian, base ring $R$: the locus where the bundle becomes trivial is represented by a closed subscheme of the chart, locally of finite presentation. It feeds the construction of the global triviality locus over a base locally of finite presentation, used in the construction of the relative Picard functor for Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isClosedImmersion_lfp_chart_iff_affineOpens_of_locallyOfFinitePresentation.lean

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

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_isClosedImmersion_lfp_chart_iff_affineOpens_of_locallyOfFinitePresentation
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hA : AbelianSchemePropertyBundle R f)
    {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation g]
    (M : RigidifiedLineBundle f (L.one (𝟙 (Spec (CommRingCat.of R)))) g) (U : X.affineOpens) :
    ∃ (ZU : Scheme.{0}) (ιU : ZU ⟶ ((U : X.Opens) : Scheme.{0})),
        IsClosedImmersion ιU ∧ LocallyOfFinitePresentation ιU ∧
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (ψU : T ⟶ ((U : X.Opens) : Scheme.{0}))
          (hψ : (ψU ≫ (U : X.Opens).ι) ≫ g = t),
          (Nonempty ((M.pullbackAlong (⟨ψU ≫ (U : X.Opens).ι, hψ⟩ : SchemeHomOver t g)).L ≅
              (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) t).L) ↔
            ∃ ψ₀ : T ⟶ ZU, ψ₀ ≫ ιU = ψU) := by sorry
