-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_nonempty_iso_unit_of_forall_transition_eq_one
-- name    : AlgebraicGeometry.Scheme.Modules.CechTrivialisation.nonempty_iso_unit_of_forall_transition_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/c16fbb47-4253-5407-a0ea-5ed9ef069221
-- title:
--   Trivial transition functions give a global trivialisation
-- statement:
--   Let $Y$ be a scheme and let $\mathcal V$ be an ordered affine cover of $Y$: a finite linearly ordered index type $\mathcal V.\iota$ together with opens $\mathcal V.U\,a$, each affine, whose supremum is $\top$. Let $\mathcal M$ be a sheaf of modules over the structure sheaf of rings of $Y$, and let $\tau$ be a Čech trivialisation of $\mathcal M$ with respect to $\mathcal V$, i.e. for each index $a$ an isomorphism between the pullback of $\mathcal M$ along the inclusion of $\mathcal V.U\,a$ and the unit module on $\mathcal V.U\,a$. For an index $s \in \mathcal V.\mathrm{Idx}\,1$, that is a strictly monotone map $\mathrm{Fin}\,2 \to \mathcal V.\iota$ picking a pair $a<b$, the transition section $\tau.\mathrm{transition}\,s \in \Gamma(Y, \mathcal V.\mathrm{inter}\,s)$ is the value at $1$ of the automorphism of the unit module on $\mathcal V.\mathrm{inter}\,s = \mathcal V.U\,a \sqcap \mathcal V.U\,b$ obtained by composing the inverse of the restriction of $\tau_a$ with the restriction of $\tau_b$. Assuming every such transition section equals $1$, the theorem asserts that the type of isomorphisms between $\mathcal M$ and the unit module `SheafOfModules.unit Y.ringCatSheaf` is nonempty; no particular isomorphism is produced.
--
--   This is the gluing step in the Čech description of the Picard group: a module with a local trivialisation whose Čech $1$-cocycle is identically $1$ is globally trivial. It is used for the comparison of trivialisations [`AlgebraicGeometry.Scheme.Modules.CechTrivialisation.nonempty_iso_of_transition_eq`](thm.html#AlgebraicGeometry.Scheme.Modules.CechTrivialisation.nonempty_iso_of_transition_eq) and, through it, in the analysis of Picard deformation cocycles along a small extension; the proof invokes the uniqueness-and-existence statement for gluing isomorphisms of modules over a cover, together with the compatibility of the pullback composition isomorphism with the canonical identification of pullbacks of the unit module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_nonempty_iso_unit_of_forall_transition_eq_one.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.CechTrivialisation.nonempty_iso_unit_of_forall_transition_eq_one
    {Y : Scheme.{u}} {𝒱 : Y.OrderedAffineCover} {𝓜 : Y.Modules}
    (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜)
    (h : ∀ s : 𝒱.Idx 1, τ.transition s = 1) :
    Nonempty (𝓜 ≅ SheafOfModules.unit Y.ringCatSheaf) := by sorry
