-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_rigidify
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.rigidify
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/2c74bec0-fccc-56a5-aa49-621bedaf5c04
-- title:
--   Rigidification of an invertible module along a section
-- statement:
--   Let $T$ and $P$ be schemes, let $\sigma : T \to P$ and $q : P \to T$ be morphisms whose composite $\sigma$ followed by $q$ is the identity of $T$ (so $\sigma$ is a section of $q$), and let $L$ be an object of the category `P.Modules` of sheaves of modules on $P$ which is invertible in the sense of the project predicate `Scheme.Modules.IsInvertible`: every point of $P$ has an open neighbourhood $U$ such that the pullback of $L$ along the inclusion $U \hookrightarrow P$ is isomorphic to the unit object `SheafOfModules.unit` of the sheaf of rings of $U$. The assertion is twofold for the module $\mathrm{rigidify}\,\sigma\,q\,L := L \otimes q^{*}\bigl((\sigma^{*}L)^{\vee}\bigr)$, where $(-)^{\vee}$ denotes the internal hom into the monoidal unit: first, this module is again invertible in the same local sense; second, the type of isomorphisms $\sigma^{*}\bigl(\mathrm{rigidify}\,\sigma\,q\,L\bigr) \cong \mathbf{1}_{T.\mathrm{Modules}}$ is nonempty, i.e. the pullback along $\sigma$ of the rigidified module is isomorphic to the monoidal unit on $T$. Only the existence of such an isomorphism is claimed; no canonical choice is produced.
--
--   This is the standard rigidification construction for the relative Picard functor: from an invertible module on $P$ one manufactures one whose pullback along the given section of $q$ is trivial. It is used to produce rigidified line bundles in the construction of the relative Picard functor, and is cited in the treatment of relative effective Cartier divisors and their associated twisting modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_rigidify.lean

import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.rigidify
    {T P : Scheme.{u}} {σ : T ⟶ P} {q : P ⟶ T} (hσq : σ ≫ q = 𝟙 T) {L : P.Modules}
    (hL : Scheme.Modules.IsInvertible L) :
    Scheme.Modules.IsInvertible (Scheme.Modules.rigidify σ q L) ∧
      Nonempty ((Scheme.Modules.pullback σ).obj (Scheme.Modules.rigidify σ q L) ≅ 𝟙_ T.Modules) := by sorry
