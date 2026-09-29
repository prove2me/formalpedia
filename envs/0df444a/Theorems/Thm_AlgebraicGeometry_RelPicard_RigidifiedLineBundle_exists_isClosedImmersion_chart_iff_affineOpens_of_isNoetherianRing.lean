-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isClosedImmersion_chart_iff_affineOpens_of_isNoetherianRing
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_isClosedImmersion_chart_iff_affineOpens_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/0a844627-0ff1-58dd-8844-43180741c7d8
-- title:
--   Triviality locus of a rigidified bundle on an affine chart
-- statement:
--   Let $R$ be a noetherian commutative ring, let $f \colon A \to \operatorname{Spec} R$ be a morphism of schemes, let $L$ be a relative group law on $f$ (functorial multiplication, unit and inverse on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $R$-points, satisfying associativity, the unit laws, left inverses, and compatibility with base change $T' \to T$), and assume the bundle of properties `AbelianSchemePropertyBundle R f`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ over a point of $\operatorname{Spec} R$ is connected, and $f$ admits some relative group law. Let $g \colon X \to \operatorname{Spec} R$ be locally of finite type, let $M$ be a rigidified line bundle for $f$, $g$ and the unit section $\varepsilon = L.\mathrm{one}$ of the identity of $\operatorname{Spec} R$ — that is, an invertible module $M.L$ on $A \times_R X$ together with a trivialisation of its pullback along the induced section $X \to A \times_R X$ — and let $U$ be an affine open of $X$. Then there are a scheme $Z_U$ and a closed immersion $\iota_U \colon Z_U \to U$ (the open subscheme $U$ regarded as a scheme) such that for every scheme $T$, every $t \colon T \to \operatorname{Spec} R$ and every $\psi_U \colon T \to U$ whose composite with $U \hookrightarrow X$ followed by $g$ equals $t$, the pullback of $M$ along $\psi_U$ followed by $U \hookrightarrow X$ has underlying module isomorphic to the unit module on $A \times_R T$ if and only if $\psi_U$ factors as $\psi_0$ followed by $\iota_U$ for some $\psi_0 \colon T \to Z_U$.
--
--   This is the see-saw statement that the locus where a rigidified line bundle on an abelian scheme becomes trivial is cut out by a closed subscheme, proved here over a single affine chart of the base $X$. It is the local input to the global version [`AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_isClosedImmersion_forall_nonempty_pullbackAlong_iso_unit_iff_of_isNoetherianRing`](thm.html#AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_isClosedImmersion_forall_nonempty_pullbackAlong_iso_unit_iff_of_isNoetherianRing), obtained by gluing the closed subschemes $Z_U$ over a cover of $X$ by affine opens, and thus to the representability of the relative Picard functor used for Jacobians with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isClosedImmersion_chart_iff_affineOpens_of_isNoetherianRing.lean

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

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_isClosedImmersion_chart_iff_affineOpens_of_isNoetherianRing
    {R : Type} [CommRing R] [IsNoetherianRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hA : AbelianSchemePropertyBundle R f)
    {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType g]
    (M : RigidifiedLineBundle f (L.one (𝟙 (Spec (CommRingCat.of R)))) g) (U : X.affineOpens) :
    ∃ (ZU : Scheme.{0}) (ιU : ZU ⟶ ((U : X.Opens) : Scheme.{0})), IsClosedImmersion ιU ∧
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (ψU : T ⟶ ((U : X.Opens) : Scheme.{0}))
          (hψ : (ψU ≫ (U : X.Opens).ι) ≫ g = t),
          (Nonempty ((M.pullbackAlong (⟨ψU ≫ (U : X.Opens).ι, hψ⟩ : SchemeHomOver t g)).L ≅
              (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) t).L) ↔
            ∃ ψ₀ : T ⟶ ZU, ψ₀ ≫ ιU = ψU) := by sorry
