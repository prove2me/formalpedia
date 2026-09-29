-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_exists_isNodeUnitModule_pullback_of_pullback_iso_unit
-- name    : AlgebraicGeometry.TwoGluedProjectiveLines.exists_isNodeUnitModule_pullback_of_pullback_iso_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/4614cd3f-8f0d-5d86-9cb1-09e6728b6f93
-- title:
--   Bundle trivial on both lines is a node-unit module
-- statement:
--   Let $\kappa$ be an algebraically closed field and let $x \colon X \to \operatorname{Spec}\kappa$ be a morphism with $X$ reduced. Let $M_1, M_2$ be two curve models of $\mathrm{RatFunc}\,\kappa$ over $\kappa$, that is, integral schemes $M_j.C$ proper and smooth of relative dimension $1$ over $\operatorname{Spec}\kappa$ together with a ring isomorphism of $\mathrm{RatFunc}\,\kappa$ with the function field compatible with the structure map, and a bijection `placeEquiv` from the closed points of $M_j.C$ onto the places of $\mathrm{RatFunc}\,\kappa$ over $\kappa$ matching stalks with valuation subrings, each finite set of points lying in an affine open. Let $i_1 \colon M_1.C \to X$ and $i_2 \colon M_2.C \to X$ be closed immersions with $i_1 \circ x = M_1.\mathrm{toBase}$, $i_2 \circ x = M_2.\mathrm{toBase}$, whose images cover $X$. Let $s \in \mathbb{N}$ and $a, b \colon \mathrm{Fin}\,s \to \kappa^\times$ with $a$ injective; assume that for each $i$ the closed point of $M_1.C$ at the place $\mathrm{placeOfPoint}(a_i)$ (the place of $t - a_i$) and the closed point of $M_2.C$ at $\mathrm{placeOfPoint}(b_i)$ have the same image in $X$, that conversely every pair $p \in M_1.C$, $q \in M_2.C$ with $i_1(p) = i_2(q)$ is such a pair, and that the scheme $M_1.C \times_X M_2.C$ is reduced. Finally let $L$ be a sheaf of modules on $X$ which is invertible (each point has a neighbourhood $U$ over which the pullback of $L$ along $U \hookrightarrow X$ is isomorphic to the unit module), and assume that the pullback of $L$ along $i_1$ is isomorphic to the pullback of the unit module of $X$ along $i_1$, and likewise for $i_2$. Then there are units $\lambda_i \in \kappa^\times$, $i \in \mathrm{Fin}\,s$, such that the pullback of $L$ along the first projection $\mathrm{pullback}(x, \mathbf{1}_{\operatorname{Spec}\kappa}) \to X$ is a node-unit module with gluing units the images of the $\lambda_i$ in $\Gamma(\operatorname{Spec}\kappa, \mathcal{O})^\times$ under the canonical identification: there exist morphisms $j_1, j_2$ from that module to the pushforwards along the base-changed immersions of the unit modules of $\mathrm{pullback}(M_1.\mathrm{toBase}, \mathbf{1})$ and $\mathrm{pullback}(M_2.\mathrm{toBase}, \mathbf{1})$ such that over every open $W$ the map $m \mapsto (j_1(m), j_2(m))$ on sections is injective with image exactly the pairs $(f,g)$ whose restrictions to each node locus satisfy $f = \lambda_i g$.
--
--   This is the statement that an invertible module on two projective lines glued transversally at $s$ nodes, trivialised on each of the two components, is recovered as the module of pairs of sections agreeing up to a unit at each node — the injectivity part of the description of $\operatorname{Pic}$ of such a curve by its gluing units. It is used in the identification of the relative Picard group of the two-glued-lines configuration, via [`AlgebraicGeometry.TwoGluedProjectiveLines.isAlgEquivZero_of_pullback_iso_unit`](thm.html#AlgebraicGeometry.TwoGluedProjectiveLines.isAlgEquivZero_of_pullback_iso_unit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedProjectiveLines_exists_isNodeUnitModule_pullback_of_pullback_iso_unit.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_TwoGluedProjectiveLinesNodeUnitModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
  NeronModelInfra AlgebraicGeometry.TwoGluedProjectiveLines

theorem AlgebraicGeometry.TwoGluedProjectiveLines.exists_isNodeUnitModule_pullback_of_pullback_iso_unit
    (κ : Type u) [Field κ] [IsAlgClosed κ]
    {X : Scheme.{u}} (x : X ⟶ Spec (.of κ)) [IsReduced X]
    (M₁ M₂ : CurveModel κ (RatFunc κ)) (i₁ : M₁.C ⟶ X) (i₂ : M₂.C ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hi₁ : i₁ ≫ x = M₁.toBase) (hi₂ : i₂ ≫ x = M₂.toBase)
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    {s : ℕ} (a b : Fin s → κˣ) (ha : Function.Injective a)
    (hnode : ∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (a i : κ))).1
                = i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (b i : κ))).1)
    (hinter : ∀ p q, i₁.base p = i₂.base q →
      ∃ i, p = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (a i))).1 ∧
        q = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint κ (b i))).1)
    (htrans : IsReduced (pullback i₁ i₂))
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (h₁ : Nonempty ((Scheme.Modules.pullback i₁).obj L ≅
      (Scheme.Modules.pullback i₁).obj (SheafOfModules.unit X.ringCatSheaf)))
    (h₂ : Nonempty ((Scheme.Modules.pullback i₂).obj L ≅
      (Scheme.Modules.pullback i₂).obj (SheafOfModules.unit X.ringCatSheaf))) :
    ∃ lam : Fin s → κˣ,
      IsNodeUnitModule x M₁ M₂ i₁ i₂ hi₁ hi₂ a b (𝟙 (Spec (.of κ)))
        (fun i => Units.map (Scheme.ΓSpecIso (.of κ)).inv.hom.toMonoidHom (lam i))
        ((Scheme.Modules.pullback (pullback.fst x (𝟙 (Spec (.of κ))))).obj L) := by sorry
