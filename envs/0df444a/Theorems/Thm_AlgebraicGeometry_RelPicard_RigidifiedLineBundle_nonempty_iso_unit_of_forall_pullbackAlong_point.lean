-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_unit_of_forall_pullbackAlong_point
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_iso_unit_of_forall_pullbackAlong_point
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/68da16c5-f60b-5694-a5c7-28876059d775
-- title:
--   Seesaw triviality of a rigidified line bundle
-- statement:
--   Let $k$ be an algebraically closed field, let $c\colon X\to\operatorname{Spec}k$ be a proper morphism with $X$ integral, and let $\varepsilon$ be a section of $c$, that is, a morphism $\operatorname{Spec}k\to X$ whose composite with $c$ is the identity of $\operatorname{Spec}k$. Let $t\colon T\to\operatorname{Spec}k$ be locally of finite type with $T$ reduced. Let $M$ be a rigidified line bundle for the data $(c,\varepsilon,t)$: a sheaf of modules $M.L$ on the fibre product $X\times_{\operatorname{Spec}k}T$ which is invertible in the sense that every point has an open neighbourhood $U$ over which the restriction of $M.L$ along $U\hookrightarrow X\times_{\operatorname{Spec}k}T$ is isomorphic to the unit sheaf, together with an isomorphism between the pullback of $M.L$ along the section $\mathrm{rigSection}$ determined by $\varepsilon$ (namely $T\to X\times_{\operatorname{Spec}k}T$ with components $t$ followed by $\varepsilon$, and $\mathrm{id}_T$) and the unit sheaf on $T$. Assume that for every $\tau\colon\operatorname{Spec}k\to T$ with $\tau$ followed by $t$ the identity, the underlying sheaf of the base change $M.\mathrm{pullbackAlong}\,\tau$, i.e. the pullback of $M.L$ along the map $X\times_{\operatorname{Spec}k}\operatorname{Spec}k\to X\times_{\operatorname{Spec}k}T$ induced by $\mathrm{id}_X$ and $\tau$, is isomorphic to the unit sheaf on $X\times_{\operatorname{Spec}k}\operatorname{Spec}k$ (the pullback of $c$ along $\mathrm{id}_{\operatorname{Spec}k}$). Then $M.L$ is isomorphic to the unit sheaf on $X\times_{\operatorname{Spec}k}T$. The conclusion asserts only an isomorphism of the underlying invertible sheaves, not compatibility with the rigidifications.
--
--   This is the seesaw theorem in the form: a line bundle on $X\times T$ that is trivial on the slice $\{\varepsilon\}\times T$ and on every slice $X\times\{\tau\}$ over a $k$-point $\tau$ of $T$ is trivial. It is used in the treatment of polarisations and the relative Picard functor, for instance to characterise membership in the identity component of the Picard group and to compare Mumford bundles with pullbacks along addition maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_unit_of_forall_pullbackAlong_point.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_iso_unit_of_forall_pullbackAlong_point
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of k))
    [IsProper c] [IsIntegral X] (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t] [IsReduced T]
    (M : RigidifiedLineBundle c ε t)
    (hM : ∀ τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) t,
      Nonempty ((M.pullbackAlong τ).L ≅
        SheafOfModules.unit (Limits.pullback c (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf)) :
    Nonempty (M.L ≅ SheafOfModules.unit (Limits.pullback c t).ringCatSheaf) := by sorry
