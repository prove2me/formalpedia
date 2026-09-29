-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_closedCover_of_forall_pullbackSection_eq
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_unit_of_closedCover_of_forall_pullbackSection_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/a4a88794-adc4-5f3e-a43a-af7d45db9285
-- title:
--   Gluing trivialisations of a line bundle over a two-component cover
-- statement:
--   Let $k$ be an algebraically closed field, $X$ a reduced scheme with a structure morphism $x \colon X \to \operatorname{Spec} k$ that is locally of finite type, and let $i_1 \colon Y_1 \to X$ and $i_2 \colon Y_2 \to X$ be closed immersions whose topological images cover $X$ (the union of the ranges of the underlying continuous maps is all of $X$); assume further that the fibre product $Y_1 \times_X Y_2$ is reduced. Let $L$ be an $\mathcal{O}_X$-module which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ on which the restriction of $L$ along $U \hookrightarrow X$ is isomorphic to the unit module, and suppose given isomorphisms $\tau_\nu \colon i_\nu^{*} L \cong i_\nu^{*}(\mathcal{O}_X)$ for $\nu = 1,2$, i.e. isomorphisms onto the pullback of the monoidal unit of $X$-modules. Each $\tau_\nu$ determines a global section $(\mathrm{pullbackUnitIso}\, i_\nu)^{-1} \circ \tau_\nu^{-1}$ of $i_\nu^{*} L$ (a map from the unit module), and these may be pulled back to $Y_1 \times_X Y_2$ along the two projections and compared there via the canonical isomorphisms $\mathrm{pr}_1^{*} i_1^{*} L \cong (\mathrm{pr}_1 \circ i_1)^{*} L = (\mathrm{pr}_2 \circ i_2)^{*} L \cong \mathrm{pr}_2^{*} i_2^{*} L$ supplied by `Scheme.Modules.pullbackComp` and `Scheme.Modules.pullbackCongr` applied to the pullback square condition. The hypothesis is that for every morphism $p \colon \operatorname{Spec} k \to Y_1 \times_X Y_2$ which is a section of $\mathrm{pr}_1$ followed by $i_1$ followed by $x$, the two resulting sections of $p^{*}$ of that module agree. The conclusion is that the type of isomorphisms $L \cong \mathcal{O}_X$ (the unit module of the sheaf of rings of $X$) is nonempty.
--
--   This is the gluing step in the computation of the Picard group of a scheme covered by two closed subschemes: a line bundle trivial on each of the two pieces is trivial on the whole as soon as the two trivialisations can be chosen to agree at the $k$-rational points of the (reduced) intersection. It is used in the analysis of two projective lines glued along a finite set of nodes, where it feeds into [`AlgebraicGeometry.TwoGluedProjectiveLines.exists_nodeRatioHom`](thm.html#AlgebraicGeometry.TwoGluedProjectiveLines.exists_nodeRatioHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_closedCover_of_forall_pullbackSection_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_unit_of_closedCover_of_forall_pullbackSection_eq
    {k : Type u} [Field k] [IsAlgClosed k] {X Y₁ Y₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    [IsReduced X] [LocallyOfFiniteType x]
    (i₁ : Y₁ ⟶ X) (i₂ : Y₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hcover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) (htrans : IsReduced (Limits.pullback i₁ i₂))
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (τ₁ : (Scheme.Modules.pullback i₁).obj L ≅ (Scheme.Modules.pullback i₁).obj (𝟙_ X.Modules))
    (τ₂ : (Scheme.Modules.pullback i₂).obj L ≅ (Scheme.Modules.pullback i₂).obj (𝟙_ X.Modules))
    (hpts : ∀ p : Spec (CommRingCat.of k) ⟶ Limits.pullback i₁ i₂, p ≫ (Limits.pullback.fst i₁ i₂ ≫ i₁ ≫ x) = 𝟙 _ →
      Scheme.Modules.pullbackSection p
          (Scheme.Modules.pullbackSection (Limits.pullback.fst i₁ i₂) ((Scheme.Modules.pullbackUnitIso i₁).inv ≫ τ₁.inv) ≫
            ((Scheme.Modules.pullbackComp (Limits.pullback.fst i₁ i₂) i₁).app L).hom ≫
              ((Scheme.Modules.pullbackCongr (Limits.pullback.condition (f := i₁) (g := i₂))).app L).hom) =
        Scheme.Modules.pullbackSection p
          (Scheme.Modules.pullbackSection (Limits.pullback.snd i₁ i₂) ((Scheme.Modules.pullbackUnitIso i₂).inv ≫ τ₂.inv) ≫
            ((Scheme.Modules.pullbackComp (Limits.pullback.snd i₁ i₂) i₂).app L).hom)) :
    Nonempty (L ≅ SheafOfModules.unit X.ringCatSheaf) := by sorry
