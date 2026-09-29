-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_rigidify_iso_of_nonempty_pullback_iso_unit
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_rigidify_iso_of_nonempty_pullback_iso_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/82eaf627-5af9-598c-aab2-bc68da423cd1
-- title:
--   Rigidification is trivial when σ^*L is trivial
-- statement:
--   Let $T$ and $P$ be schemes, let $\sigma : T \to P$ and $q : P \to T$ be morphisms of schemes, and let $L$ be an object of $P.\mathrm{Modules}$, the category of sheaves of $\mathcal{O}_P$-modules. Assume that the pullback of $L$ along $\sigma$ is trivial in the weak sense that the type of isomorphisms $(\sigma^*L) \cong \mathbf{1}_{T.\mathrm{Modules}}$ is nonempty, where $\mathbf{1}$ is the monoidal unit, i.e. the structure sheaf. The conclusion asserts that the type of isomorphisms $\mathrm{rigidify}\,\sigma\,q\,L \cong L$ is nonempty, where by definition $\mathrm{rigidify}\,\sigma\,q\,L = L \otimes q^*\bigl((\sigma^*L)^\vee\bigr)$ and the dual $(-)^\vee$ of an object is the internal hom $\underline{\mathrm{Hom}}(-,\mathbf{1})$ into the monoidal unit of the closed monoidal category of sheaves of modules on the relevant scheme. Both hypothesis and conclusion are statements of nonemptiness, so no specific isomorphism is named; the conclusion produces an unspecified isomorphism, not a canonical or natural one.
--
--   This records that the rigidification operation $L \mapsto L \otimes q^*(\sigma^*L)^\vee$ along a section-type morphism $\sigma$ and a structure morphism $q$ leaves $L$ unchanged up to isomorphism as soon as $\sigma^*L$ is already trivial, the normalisation used for rigidified line bundles in the relative Picard formalism. It is used in the relative Picard development, for instance in the comparison of Poincaré-type objects with rigidifications and in the computations of deformation classes over dual numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_rigidify_iso_of_nonempty_pullback_iso_unit.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesRigidify

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.nonempty_rigidify_iso_of_nonempty_pullback_iso_unit
    {T P : Scheme.{u}} (σ : T ⟶ P) (q : P ⟶ T) (L : P.Modules)
    (hσL : Nonempty ((Scheme.Modules.pullback σ).obj L ≅ 𝟙_ T.Modules)) :
    Nonempty (Scheme.Modules.rigidify σ q L ≅ L) := by sorry
