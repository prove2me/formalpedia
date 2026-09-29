-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover
-- name    : AlgebraicGeometry.Scheme.Modules.toDescentData_essSurj_of_openCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/45ed974b-ef1c-5e87-b7a2-b2570ea03da2
-- title:
--   Effectivity of Zariski descent data for sheaves of modules
-- statement:
--   Let $Y$ be a scheme, let $\iota$ be a type (its universe is independent of the universe of the schemes), let $V : \iota \to \mathrm{Scheme}$ be a family of schemes, and let $g_i \colon V_i \to Y$ be morphisms, each assumed to be an open immersion. Assume the family is jointly surjective on points: for every point $y$ of $Y$ there is an index $i$ with $y$ in the range of the underlying continuous map of $g_i$. Consider the pseudofunctor obtained from `Scheme.Modules.pseudofunctor` by composing with `Bicategory.Adj.forget₁`, that is, the assignment sending a scheme $X$ to the category of $\mathcal{O}_X$-modules and a morphism $f$ to its pull-back functor $f^{*}$, and let `toDescentData` be the associated comparison functor from $\mathcal{O}_Y$-modules to descent data relative to the family $(g_i)_i$. The conclusion is that this comparison functor is essentially surjective: every descent datum for the family is isomorphic to the descent datum arising from some $\mathcal{O}_Y$-module.
--
--   This is the "objects glue" half of effective Zariski descent for sheaves of modules: combined with full faithfulness of the same comparison functor it expresses that $X \mapsto \mathrm{Mod}(\mathcal{O}_X)$ is a stack for the Zariski topology. It is used to construct modules, and in particular invertible modules, from local data together with compatible pull-back isomorphisms satisfying the cocycle condition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_toDescentData_essSurj_of_openCover.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.toDescentData_essSurj_of_openCover
    {Y : Scheme.{u}} {ι : Type v} {V : ι → Scheme.{u}} (g : ∀ i, V i ⟶ Y) [∀ i, IsOpenImmersion (g i)]
    (hg : ∀ y : Y, ∃ i, y ∈ Set.range (g i).base) :
    (((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData g).EssSurj := by sorry
