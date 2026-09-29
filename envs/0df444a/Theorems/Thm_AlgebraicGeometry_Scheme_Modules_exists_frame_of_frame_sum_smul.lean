-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_sum_smul
-- name    : AlgebraicGeometry.Scheme.Modules.exists_frame_of_frame_sum_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/bc74b4c4-9a2b-50b4-b675-420bee202ec1
-- title:
--   A frame among the terms of a frame sum
-- statement:
--   Let $X$ be a scheme, let $M$ be a sheaf of $\mathcal O_X$-modules on $X$ (an object of `X.Modules`), let $\iota$ be a finite index type, let $a : \iota \to \Gamma(X,\top)$ be a family of global functions, let $t : \iota \to \Gamma(M,\top)$ be a family of global sections of $M$, and let $x$ be a point of $X$. Assume that the global section $\sum_j a_j \cdot t_j$ is a frame of $M$ near $x$ in the following sense: there is an open $U \subseteq X$ with $x \in U$ such that for every open $V \le U$ the map $\Gamma(X,V) \to \Gamma(M,V)$, $g \mapsto g \cdot \bigl(\sum_j a_j \cdot t_j\bigr)|_V$, obtained by restricting along $V \le \top$ and multiplying, is bijective. The conclusion is that some single member of the family is already such a frame near $x$: there exist an index $j$ and an open $U \subseteq X$ with $x \in U$ such that for every open $V \le U$ the map $\Gamma(X,V) \to \Gamma(M,V)$, $g \mapsto g \cdot t_j|_V$, is bijective. No invertibility assumption on $M$ is imposed beyond what the hypothesis gives locally.
--
--   The bijectivity condition appearing here is the pointwise notion of a local frame (a local trivialisation $\mathcal O_V \xrightarrow{\ \sim\ } M|_V$ given by a section), and the statement says that this property passes from a finite $\Gamma(X,\mathcal O_X)$-combination of global sections to one of its terms. It is used in the construction of frames on invertible modules and in the reframing of framed polarised abelian schemes, for instance by [`AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isReframe`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isReframe) and by [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isFrameOn_of_forall_geometricFibre_exists_isFrameOn_of_forall_eq_sum_smul_pullbackLocalSection`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isFrameOn_of_forall_geometricFibre_exists_isFrameOn_of_forall_eq_sum_smul_pullbackLocalSection).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_sum_smul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_frame_of_frame_sum_smul
    {X : Scheme.{u}} (M : X.Modules) {ι : Type*} [Fintype ι] (a : ι → Γ(X, ⊤)) (t : ι → Γ(M, ⊤)) (x : X)
    (h : ∃ U : X.Opens, x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
      Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (∑ j, a j • t j) : Γ(M, V))) :
    ∃ (j : ι) (U : X.Opens), x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
      Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (t j) : Γ(M, V)) := by sorry
