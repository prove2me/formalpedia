-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_iso_of_forall_nonempty_pullback_iso_of_isPullback_pi
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_iso_of_forall_nonempty_pullback_iso_of_isPullback_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/b64862f8-a104-5521-a322-6e865da5291c
-- title:
--   Gluing module isomorphisms over a finite product of rings
-- statement:
--   Let $k$ be a natural number and let $C_0,\dots,C_{k-1}$ be commutative rings, indexed by $\mathrm{Fin}\,k$. Let $X$ be a scheme together with a morphism $g : X \to \operatorname{Spec}\bigl(\prod_i C_i\bigr)$, and for each $i$ let $X_i$ be a scheme with morphisms $g_i : X_i \to \operatorname{Spec} C_i$ and $v_i : X_i \to X$ such that the square formed by $v_i$, $g_i$, $g$ and $\operatorname{Spec}$ of the $i$-th projection $\prod_j C_j \to C_i$ is cartesian, i.e. $X_i$ together with $v_i$ and $g_i$ realises the fibre product $X \times_{\operatorname{Spec}\prod_j C_j} \operatorname{Spec} C_i$. Let $M$ and $N$ be sheaves of modules on $X$, that is, objects of `X.Modules`. Assume that for every $i$ the pullbacks along $v_i$ satisfy $v_i^* M \cong v_i^* N$, the hypothesis being the non-emptiness of the type of such isomorphisms, with no compatibility imposed between the isomorphisms for different $i$. The conclusion is that the type of isomorphisms $M \cong N$ in `X.Modules` is non-empty; no particular isomorphism is constructed.
--
--   This is the gluing half of Zariski descent for modules along a decomposition of $X$ induced by a finite product decomposition of a base ring: the morphisms $v_i$ exhibit $X$ as a disjoint union of open subschemes, over which isomorphism classes of modules may be compared piecewise. It is used in the study of local isomorphism on the base, via [`AlgebraicGeometry.Polarisation.LocIsoOnBase.exists_forall_nonempty_pullback_iso_of_isPullback_pi_localizationAway`](thm.html#AlgebraicGeometry.Polarisation.LocIsoOnBase.exists_forall_nonempty_pullback_iso_of_isPullback_pi_localizationAway).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_iso_of_forall_nonempty_pullback_iso_of_isPullback_pi.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.nonempty_iso_of_forall_nonempty_pullback_iso_of_isPullback_pi
    {k : ℕ} (C : Fin k → Type u) [∀ i, CommRing (C i)]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of (∀ i, C i)))
    {Xi : Fin k → Scheme.{u}} (gi : ∀ i, Xi i ⟶ Spec (CommRingCat.of (C i))) (v : ∀ i, Xi i ⟶ X)
    (hv : ∀ i, IsPullback (v i) (gi i) g (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))))
    (M N : X.Modules)
    (h : ∀ i, Nonempty ((Scheme.Modules.pullback (v i)).obj M ≅ (Scheme.Modules.pullback (v i)).obj N)) :
    Nonempty (M ≅ N) := by sorry
