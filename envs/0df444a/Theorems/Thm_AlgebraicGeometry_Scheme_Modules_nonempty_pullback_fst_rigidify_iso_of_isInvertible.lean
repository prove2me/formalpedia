-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_fst_rigidify_iso_of_isInvertible
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_pullback_fst_rigidify_iso_of_isInvertible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/5d2b6c0c-1e2e-5742-9e53-e04bf11b5472
-- title:
--   Rigidification is invisible on fibres over field-valued points
-- statement:
--   Let $T$ and $P$ be schemes, let $\sigma\colon T\to P$ and $q\colon P\to T$ be morphisms of schemes, and let $L$ be an $\mathcal O_P$-module which is invertible in the sense that every point of $P$ has an open neighbourhood $U$ such that the restriction of $L$ along the inclusion $U\hookrightarrow P$ is isomorphic to the unit module $\mathcal O_U$. Let $k$ be a field and let $x\colon \operatorname{Spec} k\to T$ be a morphism. Write $\mathrm{rigidify}\,\sigma\,q\,L$ for the module $L\otimes q^{*}\bigl((\sigma^{*}L)^{\vee}\bigr)$ on $P$, the dual being the internal hom from $\sigma^{*}L$ into the unit module, and let $j\colon P\times_T\operatorname{Spec} k\to P$ be the first projection of the fibre product of $q$ and $x$. The assertion is that the type of isomorphisms $j^{*}\bigl(L\otimes q^{*}((\sigma^{*}L)^{\vee})\bigr)\cong j^{*}L$ of modules on $P\times_T\operatorname{Spec} k$ is nonempty. No compatibility between $\sigma$ and $q$ (such as $\sigma$ being a section of $q$) is assumed, and no invertibility conclusion about the fibre restrictions is recorded: only the bare existence of an isomorphism is produced.
--
--   This is the fibrewise triviality of the rigidification correction factor: rigidifying an invertible module along a morphism $\sigma$ changes it by a module pulled back from the base $T$, hence not at all on the fibre over a field-valued point of $T$. It is used in the construction and study of the relative Picard functor, where fibrewise conditions (such as membership in $\mathrm{Pic}^0$) imposed on a re-rigidified bundle are tested through the un-rigidified one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_fst_rigidify_iso_of_isInvertible.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.nonempty_pullback_fst_rigidify_iso_of_isInvertible
    {T P : Scheme.{u}} (σ : T ⟶ P) (q : P ⟶ T) (L : P.Modules) (hL : Scheme.Modules.IsInvertible L)
    (k : Type u) [Field k] (x : Spec (CommRingCat.of k) ⟶ T) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst q x)).obj (Scheme.Modules.rigidify σ q L) ≅
      (Scheme.Modules.pullback (pullback.fst q x)).obj L) := by sorry
