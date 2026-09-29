-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_shortExact_ker_module_tensor_of_isClosedImmersion
-- name    : AlgebraicGeometry.Scheme.Modules.exists_shortExact_ker_module_tensor_of_isClosedImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/37b625df-9e54-5295-b029-6d20f0844fe1
-- title:
--   Closed-subscheme exact sequence tensored by a locally free module
-- statement:
--   Let $i\colon Z \to X$ be a closed immersion of schemes, let $n$ be a natural number, and let $F$ be a sheaf of modules over the structure sheaf of $X$ which is locally free of rank $n$ in the sense that every point $x \in X$ has an open neighbourhood $U$ for which the pullback of $F$ along the inclusion $U \hookrightarrow X$ admits an isomorphism with the free module on $\mathrm{ULift}(\mathrm{Fin}\,n)$. Then there exists a short complex $S$ of modules on $X$ which is short exact (its first map is a monomorphism, its last map an epimorphism, and the complex is exact in the middle), together with the assertion that each of the following three isomorphism types is nonempty: $S.X_1$ is isomorphic to $\mathcal I \otimes F$, where $\mathcal I$ is the module attached to the ideal sheaf datum of $i$, namely the kernel of the canonical map from the unit module $\mathcal O_X$ to the pushforward along $i$ of the unit module $\mathcal O_Z$; $S.X_2$ is isomorphic to $F$; and $S.X_3$ is isomorphic to the pushforward along $i$ of the pullback along $i$ of $F$. Only the existence of these isomorphisms is asserted, not any particular choice of them, and the maps of $S$ are not further specified.
--
--   This is the closed-subscheme (ideal-sheaf) exact sequence $0 \to \mathcal I \to \mathcal O_X \to i_*\mathcal O_Z \to 0$ tensored with a locally free module $F$, the right-hand term being identified with $i_*i^*F$ by the projection formula for the closed immersion $i$. It is used in the computation of Euler characteristics of modules twisted by an invertible ideal sheaf and in the construction of short exact sequences attached to a section of a relative curve in the relative Picard theory.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_shortExact_ker_module_tensor_of_isClosedImmersion.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_shortExact_ker_module_tensor_of_isClosedImmersion
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] {n : ℕ} (F : X.Modules)
    (hF : Scheme.Modules.IsLocallyFreeOfRank n F) :
    ∃ S : ShortComplex X.Modules, S.ShortExact ∧
      Nonempty (S.X₁ ≅ i.ker.module ⊗ F) ∧ Nonempty (S.X₂ ≅ F) ∧
      Nonempty (S.X₃ ≅ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj F)) := by sorry
