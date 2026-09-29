-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_unit_iff_forall_openCover
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_iso_unit_iff_forall_openCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/db4d1fc5-cb42-55c6-a70d-b5cc78d15b71
-- title:
--   Triviality of a rigidified line bundle is Zariski-local on the base
-- statement:
--   Let $R$ be a commutative ring, let $f : A \to \operatorname{Spec} R$ be a scheme over $\operatorname{Spec} R$, let $L$ be a relative group law on $f$ (a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $R$-morphisms to $A$, natural in $T$), and let $hA$ assert that $f$ is smooth and proper, has connected fibres over every point of $\operatorname{Spec} R$, and admits some relative group law. Write $\varepsilon = L.\mathrm{one}$ at $\mathbb 1_{\operatorname{Spec} R}$ for the unit section $\operatorname{Spec} R \to A$. Let $g : X \to \operatorname{Spec} R$ and let $M$ consist of an invertible module on $A \times_R X$ together with a trivialisation of its restriction along the rigidifying section $\varepsilon \times X$. Let $t : T \to \operatorname{Spec} R$, let $\psi : T \to X$ satisfy $\psi$ followed by $g$ equals $t$, and let $\mathcal U$ be an open cover of $T$. Then the underlying module of the base change of $M$ to $A \times_R T$ is isomorphic to the unit (structure-sheaf) module on $A \times_R T$ if and only if for every index $j$ of $\mathcal U$ the base change of $M$ along $\mathcal U_j \to T \to X$ has underlying module isomorphic to the unit module on $A \times_R \mathcal U_j$. The isomorphisms asserted are of the underlying modules only, not of rigidified bundles.
--
--   This is the statement that triviality of a rigidified line bundle on an abelian scheme times a test scheme is Zariski-local on the test scheme, the descent step that makes the relative Picard functor $\mathrm{Pic}^0$ a sheaf for the Zariski topology. It is used in the study of charts for the relative Picard scheme, and feeds the construction of the Jacobian with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_unit_iff_forall_openCover.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_iso_unit_iff_forall_openCover
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hA : AbelianSchemePropertyBundle R f)
    {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle f (L.one (𝟙 (Spec (CommRingCat.of R)))) g)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (ψ : SchemeHomOver t g) (𝒰 : T.OpenCover) :
    Nonempty ((M.pullbackAlong ψ).L ≅
        (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) t).L) ↔
      ∀ j : 𝒰.I₀, Nonempty ((M.pullbackAlong
          (⟨𝒰.f j ≫ ψ.1, by rw [Category.assoc, ψ.2]⟩ : SchemeHomOver (𝒰.f j ≫ t) g)).L ≅
        (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) (𝒰.f j ≫ t)).L) := by sorry
