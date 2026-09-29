-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_mem_nonempty_pullback_inf_iso_unit_of_uniqueFactorizationMonoid_stalk
-- name    : AlgebraicGeometry.Scheme.Modules.exists_mem_nonempty_pullback_inf_iso_unit_of_uniqueFactorizationMonoid_stalk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/809573a4-7ba2-5b58-b8ac-feb34fbda1dd
-- title:
--   Triviality of a line bundle near a factorial point
-- statement:
--   Let $X$ be a scheme (in a fixed universe) which is integral and locally Noetherian, let $W$ be an open subset of $X$, and let $\mathcal{L}$ be an object of `X.Modules`, i.e. a sheaf of modules over the structure sheaf of rings `X.ringCatSheaf`. Assume that $\mathcal{L}$ is locally trivial along $W$ in the following sense: for every $x \in W$ there is an open $U$ of $X$ with $x \in U$, $U \le W$, and such that the pullback of $\mathcal{L}$ along the open immersion $U.\iota : U \to X$ is isomorphic, as a sheaf of modules on $U$, to the unit module `SheafOfModules.unit` of `(U : Scheme).ringCatSheaf`, i.e. the structure sheaf of $U$ viewed as a module over itself (the isomorphism being asserted only through nonemptiness of the type of isomorphisms). Let $z$ be a point of $X$ whose stalk ring `X.presheaf.stalk z` is a unique factorisation monoid. Then there exists an open $V$ of $X$ with $z \in V$ such that the pullback of $\mathcal{L}$ along the open immersion $(W \sqcap V).\iota$ is isomorphic to the unit module of the structure sheaf of the open subscheme $W \cap V$. No condition is imposed on $V$ relative to $W$, and nothing is assumed about $\mathcal{L}$ outside $W$.
--
--   This is the statement that a module which is an invertible sheaf over an open set $W$ becomes trivial on $W \cap V$ for some neighbourhood $V$ of any point with factorial local ring — triviality of the Picard group of a local UFD, spread out from the local ring to a neighbourhood. It feeds the construction of rigidified line bundles and the relative Picard functor, being used by [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isInvertible_pullback_iso_of_isOpenImmersion_of_uniqueFactorizationMonoid_stalk`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isInvertible_pullback_iso_of_isOpenImmersion_of_uniqueFactorizationMonoid_stalk).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_mem_nonempty_pullback_inf_iso_unit_of_uniqueFactorizationMonoid_stalk.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_mem_nonempty_pullback_inf_iso_unit_of_uniqueFactorizationMonoid_stalk
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (W : X.Opens) {𝓛 : X.Modules}
    (hW : ∀ x ∈ W, ∃ U : X.Opens, x ∈ U ∧ U ≤ W ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj 𝓛 ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf))
    (z : X) (hz : UniqueFactorizationMonoid (X.presheaf.stalk z)) :
    ∃ V : X.Opens, z ∈ V ∧
      Nonempty ((Scheme.Modules.pullback (W ⊓ V).ι).obj 𝓛 ≅ SheafOfModules.unit (↑(W ⊓ V) : Scheme.{u}).ringCatSheaf) := by sorry
