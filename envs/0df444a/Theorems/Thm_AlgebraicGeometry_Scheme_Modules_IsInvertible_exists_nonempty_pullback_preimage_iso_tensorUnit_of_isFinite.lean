-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/7176799e-db42-5343-b1a3-afba7a03b6eb
-- title:
--   Local triviality over the target along a finite morphism
-- statement:
--   Let $q \colon Z \to T$ be a morphism of schemes (in a fixed universe) which is finite, in the sense of the Mathlib typeclass `IsFinite`, let $N$ be a module over the structure sheaf of $Z$, i.e. an object of `Z.Modules`, and suppose $N$ satisfies `Scheme.Modules.IsInvertible`, which by definition asserts that for every point $x$ of $Z$ there is an open $U \subseteq Z$ containing $x$ together with an isomorphism between the pullback of $N$ along the open immersion $U.\iota$ and the unit module `SheafOfModules.unit` of the ring sheaf of the open subscheme $U$. Let $t$ be a point of $T$. The conclusion is that there exists an open subset $W$ of $T$ with $t \in W$ such that the pullback of $N$ along the open immersion of the preimage open subscheme $q^{-1}(W) \subseteq Z$ into $Z$ is isomorphic to the monoidal unit $\mathbb{1}$ of the category of modules on $q^{-1}(W)$; the isomorphism is asserted as nonemptiness of the type of such isomorphisms, rather than exhibited.
--
--   This is the statement that an invertible module on the source of a finite morphism is trivial over the preimage of a suitable neighbourhood of any given point of the target, reflecting the fact that a finite algebra over a local ring is semilocal and hence has trivial Picard group, the trivialisation spreading out by finite presentation. It is used in the construction of the norm of an invertible module along a finite morphism and in the associated frame and kernel comparisons.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite
    {Z T : Scheme.{u}} (q : Z ⟶ T) [IsFinite q] {N : Z.Modules} (hN : Scheme.Modules.IsInvertible N) (t : T) :
    ∃ W : T.Opens, t ∈ W ∧
      Nonempty ((Scheme.Modules.pullback (q ⁻¹ᵁ W).ι).obj N ≅ 𝟙_ (↑(q ⁻¹ᵁ W) : Scheme.{u}).Modules) := by sorry
