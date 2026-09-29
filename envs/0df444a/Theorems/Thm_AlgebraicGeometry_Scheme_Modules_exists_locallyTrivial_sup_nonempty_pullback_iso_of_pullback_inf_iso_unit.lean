-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_locallyTrivial_sup_nonempty_pullback_iso_of_pullback_inf_iso_unit
-- name    : AlgebraicGeometry.Scheme.Modules.exists_locallyTrivial_sup_nonempty_pullback_iso_of_pullback_inf_iso_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/435dab54-fe18-5c6c-bc7d-1be62bab4d28
-- title:
--   Gluing a locally trivial module along a trivial chart
-- statement:
--   Let $X$ be a scheme, let $W$ and $V$ be open subsets of $X$, and let $\mathcal{L}$ be a sheaf of modules over the structure sheaf of $X$ (an object of `X.Modules`). Assume two hypotheses. First, $\mathcal{L}$ is locally trivial at every point of $W$: for each $x \in W$ there is an open $U \subseteq W$ of $X$ with $x \in U$ such that the pullback of $\mathcal{L}$ along the open immersion $U.\iota : U \to X$ admits an isomorphism to the unit sheaf of modules $\mathcal{O}_U$ of the scheme $U$ (the isomorphism is asserted only to exist, as a `Nonempty` statement, so no chosen trivialisation is part of the data). Second, the pullback of $\mathcal{L}$ along the open immersion of $W \cap V$ admits an isomorphism to the unit sheaf of modules of $W \cap V$. The conclusion asserts the existence of a sheaf of modules $\mathcal{L}'$ on $X$ with two properties: $\mathcal{L}'$ is locally trivial at every point of $W \cup V$, with trivialising opens contained in $W \cup V$ (for each $x \in W \cup V$ there is an open $U$ with $x \in U \subseteq W \cup V$ and an isomorphism, again asserted only to exist, between the pullback of $\mathcal{L}'$ to $U$ and $\mathcal{O}_U$); and the pullbacks of $\mathcal{L}'$ and of $\mathcal{L}$ along the open immersion of $W$ are isomorphic. Nothing is asserted about $\mathcal{L}'$ outside $W \cup V$.
--
--   This is Zariski gluing of $\mathcal{L}|_W$ with the trivial module on $V$ along the given trivialisation over $W \cap V$, stated entirely in terms of modules on $X$ and opens of $X$, with restriction realised as pullback along open immersions. It serves the construction of invertible modules in the relative Picard and rigidified line bundle infrastructure, being used in the extension of an invertible module across an open immersion under a unique factorisation hypothesis on the stalks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_locallyTrivial_sup_nonempty_pullback_iso_of_pullback_inf_iso_unit.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_locallyTrivial_sup_nonempty_pullback_iso_of_pullback_inf_iso_unit
    {X : Scheme.{u}} (W V : X.Opens) {𝓛 : X.Modules}
    (hW : ∀ x ∈ W, ∃ U : X.Opens, x ∈ U ∧ U ≤ W ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj 𝓛 ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf))
    (hV : Nonempty ((Scheme.Modules.pullback (W ⊓ V).ι).obj 𝓛 ≅ SheafOfModules.unit (↑(W ⊓ V) : Scheme.{u}).ringCatSheaf)) :
    ∃ 𝓛' : X.Modules,
      (∀ x ∈ W ⊔ V, ∃ U : X.Opens, x ∈ U ∧ U ≤ W ⊔ V ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj 𝓛' ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)) ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj 𝓛' ≅ (Scheme.Modules.pullback W.ι).obj 𝓛) := by sorry
