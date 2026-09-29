-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
-- name    : AlgebraicGeometry.Scheme.Modules.eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/1d60c4cd-2815-59c1-9ba0-a55b7328507c
-- title:
--   Sheaf axiom for 𝒪_X-modules on a covered open
-- statement:
--   Let $X$ be a scheme, let $M$ be an object of `X.Modules`, that is, a sheaf of $\mathcal{O}_X$-modules on $X$, let $\iota$ be an index type in the same universe, let $U : \iota \to$ `X.Opens` be a family of open subsets of $X$ and let $V$ be an open subset of $X$, subject to the two hypotheses that $U_i \le V$ for every $i$ and that $V \le \bigsqcup_i U_i$; thus the $U_i$ cover $V$ and all lie inside it. Writing $\Gamma(M, W)$ for the sections of $M$ over $W$ and using the restriction maps of the underlying presheaf of $M$ along the inclusions of opens, the conclusion is the conjunction of two assertions. First, separatedness: if $s, t \in \Gamma(M, V)$ have the same restriction to $U_i$ for every $i$, then $s = t$. Second, gluing: if $v$ assigns to each $i$ a section $v_i \in \Gamma(M, U_i)$ such that for all $i, j$ the restrictions of $v_i$ and of $v_j$ to $U_i \cap U_j$ agree, then there exists $s \in \Gamma(M, V)$ whose restriction to $U_i$ equals $v_i$ for every $i$.
--
--   This is the sheaf axiom for the sheaf of abelian groups underlying a sheaf of $\mathcal{O}_X$-modules, recorded in the $\Gamma(M, U)$ notation and restriction-map idiom used throughout the treatment of `Scheme.Modules`; it expresses $\Gamma(V, M)$ as the equaliser of $\prod_i \Gamma(U_i, M) \rightrightarrows \prod_{i,j} \Gamma(U_i \cap U_j, M)$ in the form of a uniqueness statement plus an existence statement. It is quoted by the constructions of sections of graded $\mathcal{O}$-algebras and of homomorphisms of presheaves of modules from local affine data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_eq_of_forall_map_homOfLE_eq_and_exists_of_compatible.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
    {X : Scheme.{u}} (M : X.Modules) {ι : Type u} (U : ι → X.Opens) (V : X.Opens)
    (hUV : ∀ i, U i ≤ V) (hV : V ≤ ⨆ i, U i) :
    (∀ s t : Γ(M, V),
        (∀ i, M.presheaf.map (homOfLE (hUV i)).op s = M.presheaf.map (homOfLE (hUV i)).op t) → s = t) ∧
      (∀ v : ∀ i, Γ(M, U i),
        (∀ i j, M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (v i) =
            M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (v j)) →
          ∃ s : Γ(M, V), ∀ i, M.presheaf.map (homOfLE (hUV i)).op s = v i) := by sorry
