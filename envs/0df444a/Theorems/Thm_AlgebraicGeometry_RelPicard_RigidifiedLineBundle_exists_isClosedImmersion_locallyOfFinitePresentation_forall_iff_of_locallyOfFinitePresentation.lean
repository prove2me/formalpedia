-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isClosedImmersion_locallyOfFinitePresentation_forall_iff_of_locallyOfFinitePresentation
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_isClosedImmersion_locallyOfFinitePresentation_forall_iff_of_locallyOfFinitePresentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/842636a4-e750-5123-b3cd-4884aa66f7e3
-- title:
--   Triviality locus of a rigidified line bundle is closed
-- statement:
--   Fix a commutative ring $R$ and a morphism $f \colon A \to \operatorname{Spec} R$ of schemes (all schemes in universe $0$). Let $L$ be a relative group law on $f$, i.e. a functorial group structure on the sets $\{\varphi \colon T \to A \mid \varphi \circ f = t\}$ of points of $A$ over varying $t \colon T \to \operatorname{Spec} R$, with multiplication, unit, inverse, the group axioms and naturality in $T$; let $hA$ assert that $f$ is smooth and proper, that each fibre $f^{-1}(s)$ over $s \in \operatorname{Spec} R$ is connected, and that $f$ admits some relative group law. Let $g \colon X \to \operatorname{Spec} R$ be locally of finite presentation, and let $M$ be a rigidified line bundle on $f$ over $g$ with respect to the unit section $\varepsilon = L.\mathrm{one}(\mathbf 1_{\operatorname{Spec} R})$: a module $M.L$ on the fibre product $A \times_{\operatorname{Spec} R} X$ that is locally isomorphic to the structure sheaf, together with a trivialisation of its pullback along the section $\varepsilon \times X$. The conclusion asserts the existence of a scheme $Z$ and a morphism $\iota \colon Z \to X$ which is a closed immersion and locally of finite presentation such that, for every scheme $T$, every $t \colon T \to \operatorname{Spec} R$ and every $\psi \colon T \to X$ with $\psi$ followed by $g$ equal to $t$, the pullback of $M$ along $\psi$ has underlying module isomorphic to the trivial module on $A \times_{\operatorname{Spec} R} T$ if and only if $\psi$ factors as some $\psi_0 \colon T \to Z$ followed by $\iota$.
--
--   This is the see-saw triviality locus over a general (not necessarily noetherian) base: the locus in the parameter scheme $X$ where a rigidified line bundle on $A \times_R X$ becomes trivial is represented by a closed subscheme, cut out by a closed immersion locally of finite presentation. It supplies the closedness and finite-presentation input for the treatment of polarisations and of local triviality on the base, and is used in the construction of the relative $\mathrm{Pic}^0$ of Jacobians with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isClosedImmersion_locallyOfFinitePresentation_forall_iff_of_locallyOfFinitePresentation.lean

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

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_isClosedImmersion_locallyOfFinitePresentation_forall_iff_of_locallyOfFinitePresentation
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hA : AbelianSchemePropertyBundle R f)
    {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation g]
    (M : RigidifiedLineBundle f (L.one (𝟙 (Spec (CommRingCat.of R)))) g) :
    ∃ (Z : Scheme.{0}) (ι : Z ⟶ X), IsClosedImmersion ι ∧ LocallyOfFinitePresentation ι ∧
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (ψ : SchemeHomOver t g),
        Nonempty ((M.pullbackAlong ψ).L ≅
            (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) t).L) ↔
          ∃ ψ₀ : T ⟶ Z, ψ₀ ≫ ι = ψ.1 := by sorry
