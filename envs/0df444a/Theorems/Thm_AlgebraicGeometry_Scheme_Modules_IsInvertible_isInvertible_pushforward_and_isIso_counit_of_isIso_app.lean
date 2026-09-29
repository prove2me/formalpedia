-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isInvertible_pushforward_and_isIso_counit_of_isIso_app
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.isInvertible_pushforward_and_isIso_counit_of_isIso_app
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/b66f7343-91a1-552b-9dcd-7bc7969def3f
-- title:
--   Descent of an invertible module along a contraction
-- statement:
--   Let $f : Y \to X$ be a morphism of schemes, let $U$ be an open subscheme of $X$ such that the restriction $f \mid_U : f^{-1}(U) \to U$ is an isomorphism, and let $(W_i)_{i \in \iota}$ be a family of open subschemes of $X$, indexed by an arbitrary type, with $U \sqcup \bigsqcup_i W_i = \top$ in the lattice of opens of $X$, and such that for every index $i$ and every open $V \le W_i$ the map on sections $f^\sharp_V : \Gamma(X, V) \to \Gamma(Y, f^{-1}V)$ is an isomorphism of rings. Let $L$ be a module over the structure sheaf of $Y$ which is invertible in the sense that every point of $Y$ has an open neighbourhood $V$ for which the pullback of $L$ along the inclusion $V \hookrightarrow Y$ is isomorphic to the unit module over the structure sheaf of $V$, and assume in addition that for each $i$ the pullback of $L$ along the inclusion $f^{-1}(W_i) \hookrightarrow Y$ is isomorphic to the unit module over the structure sheaf of $f^{-1}(W_i)$. Then the pushforward $f_*L$ is invertible in the same local sense, and the counit $f^*f_*L \to L$ of the pullback–pushforward adjunction at $L$ is an isomorphism.
--
--   This is the formal half of the classical statement that a line bundle on a contraction or resolution $f : Y \to X$, trivial near each contracted fibre and with $\mathcal{O}_X \to f_*\mathcal{O}_Y$ an isomorphism there, is the pullback of an invertible module on $X$; the geometric inputs appear here as hypotheses. It is used to produce the invertible descended module together with the comparison isomorphism in [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app), within the infrastructure for the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isInvertible_pushforward_and_isIso_counit_of_isIso_app.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.isInvertible_pushforward_and_isIso_counit_of_isIso_app
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) (hU : IsIso (f ∣_ U))
    {ι : Type v} (W : ι → X.Opens) (hcov : U ⊔ ⨆ i, W i = ⊤)
    (hO : ∀ (i : ι) (V : X.Opens), V ≤ W i → IsIso (f.app V))
    (L : Y.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hW : ∀ i, Nonempty ((Scheme.Modules.pullback (f ⁻¹ᵁ (W i)).ι).obj L ≅
      SheafOfModules.unit (f ⁻¹ᵁ (W i)).toScheme.ringCatSheaf)) :
    Scheme.Modules.IsInvertible ((Scheme.Modules.pushforward f).obj L) ∧
      IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app L) := by sorry
