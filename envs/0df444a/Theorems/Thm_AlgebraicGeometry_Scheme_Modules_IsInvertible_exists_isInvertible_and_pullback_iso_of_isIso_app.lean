-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isInvertible_and_pullback_iso_of_isIso_app
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/764eccb2-0890-5894-8c87-264cad32e3c6
-- title:
--   Descent of a line bundle along a contraction, existence form
-- statement:
--   Let $f : Y \to X$ be a morphism of schemes and let $U$ be an open subscheme of $X$ such that the induced morphism $f \mid_U : f^{-1}U \to U$ is an isomorphism. Let $(W_i)_{i \in \iota}$ be a family of open subschemes of $X$, indexed by an arbitrary type, whose union together with $U$ is all of $X$, i.e. $U \sqcup \bigsqcup_i W_i = \top$ in the frame of opens of $X$, and assume that for every $i$ and every open $V \le W_i$ the map on sections $f^\sharp_V : \Gamma(V, \mathcal{O}_X) \to \Gamma(f^{-1}V, \mathcal{O}_Y)$ is an isomorphism. Let $L$ be a sheaf of modules on $Y$ which is invertible in the sense of the project's predicate `Scheme.Modules.IsInvertible`: every point of $Y$ has an open neighbourhood $V$ such that the pullback of $L$ along the inclusion $V \hookrightarrow Y$ is isomorphic to the unit sheaf of modules of $V$. Assume moreover that for each $i$ the pullback of $L$ along the inclusion $f^{-1}(W_i) \hookrightarrow Y$ is isomorphic to the unit sheaf of modules on $f^{-1}(W_i)$. Then there exists a sheaf of modules $M$ on $X$ which is invertible in the same sense and for which the pullback of $M$ along $f$ is isomorphic to $L$.
--
--   This is the existence form of descent of line bundles along a contraction: a line bundle on $Y$ that is trivial on the preimage of each $W_i$, for a morphism which is an isomorphism over $U$ and whose structure-sheaf map is an isomorphism on all opens inside the $W_i$, comes from $X$. It is the shape in which descent along the Deligne–Rapoport resolution is used, being cited in the construction of line bundles on the resolved model from ones whose exceptional degrees vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isInvertible_and_pullback_iso_of_isIso_app.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) (hU : IsIso (f ∣_ U))
    {ι : Type v} (W : ι → X.Opens) (hcov : U ⊔ ⨆ i, W i = ⊤)
    (hO : ∀ (i : ι) (V : X.Opens), V ≤ W i → IsIso (f.app V))
    (L : Y.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hW : ∀ i, Nonempty ((Scheme.Modules.pullback (f ⁻¹ᵁ (W i)).ι).obj L ≅
      SheafOfModules.unit (f ⁻¹ᵁ (W i)).toScheme.ringCatSheaf)) :
    ∃ M : X.Modules, Scheme.Modules.IsInvertible M ∧ Nonempty ((Scheme.Modules.pullback f).obj M ≅ L) := by sorry
