-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_nonempty_pullback_baseChangeSnd_iso_unit_of_forall_point
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_nonempty_pullback_baseChangeSnd_iso_unit_of_forall_point
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/c76519f4-fbe3-573a-81b2-a9fc700a6aff
-- title:
--   Local seesaw: fibrewise trivial invertible sheaf is locally trivial
-- statement:
--   Let $k$ be an algebraically closed field, let $c : X \to \operatorname{Spec} k$ be a proper morphism of schemes with $X$ integral, and let $t : T \to \operatorname{Spec} k$ be locally of finite type with $T$ reduced. Let $L$ be a sheaf of modules on the fibre product $X \times_{\operatorname{Spec} k} T$ (the categorical pullback of $c$ and $t$) which is invertible in the sense that every point of that scheme has an open neighbourhood $U$ over which the restriction of $L$ along $U \hookrightarrow X \times_{\operatorname{Spec} k} T$ is isomorphic to the unit sheaf of modules on $U$. Assume that for every $k$-point of $T$, that is, every morphism $\tau : \operatorname{Spec} k \to T$ with $\tau$ followed by $t$ equal to the identity of $\operatorname{Spec} k$, the pullback of $L$ along the induced map $X \times_{\operatorname{Spec} k} \operatorname{Spec} k \to X \times_{\operatorname{Spec} k} T$ (identity on $X$, $\tau$ on the base; here the source is the pullback of $c$ along the identity of $\operatorname{Spec} k$) admits an isomorphism with the unit sheaf of modules on that source. Then for every point $x$ of $T$ there is an open subscheme $U$ of $T$ containing $x$ such that the pullback of $L$ along the map $X \times_{\operatorname{Spec} k} U \to X \times_{\operatorname{Spec} k} T$ induced by the open immersion $U \hookrightarrow T$ admits an isomorphism with the unit sheaf of modules on $X \times_{\operatorname{Spec} k} U$, where the fibre product over $U$ is formed with respect to the composite of the open immersion with $t$.
--
--   This is the analytic half of the seesaw theorem in local form: an invertible sheaf on $X \times_k T$ whose restriction to every fibre $X \times_k \{\tau\}$ over a $k$-point is trivial is trivial over a neighbourhood of each point of $T$. It feeds the construction of rigidified line bundles for the relative Picard functor, being cited by [`AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_iso_unit_of_forall_pullbackAlong_point`](thm.html#AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_iso_unit_of_forall_pullbackAlong_point), where the Zariski sheaf property of rigidified bundles upgrades local triviality to global triviality.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_nonempty_pullback_baseChangeSnd_iso_unit_of_forall_point.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_nonempty_pullback_baseChangeSnd_iso_unit_of_forall_point
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of k))
    [IsProper c] [IsIntegral X]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t] [IsReduced T]
    (L : (Limits.pullback c t).Modules) (hL : Scheme.Modules.IsInvertible L)
    (htriv : ∀ τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) t,
      Nonempty ((Scheme.Modules.pullback (baseChangeSnd c τ)).obj L ≅
        SheafOfModules.unit (Limits.pullback c (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf))
    (x : T) :
    ∃ U : T.Opens, x ∈ U ∧ Nonempty ((Scheme.Modules.pullback
        (baseChangeSnd c (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ t) t))).obj L ≅
      SheafOfModules.unit (Limits.pullback c (U.ι ≫ t)).ringCatSheaf) := by sorry
