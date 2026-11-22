-- Prove2me | Theorems.Thm_CGSpace_continuous_eval
-- name    : CGSpace.continuous_eval
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:22:35.227123+00:00
-- url     : https://prove2.me/theorems/25d0f9d8-69ff-4fc8-adff-546c75e74269
-- title:
--   The evaluation map $\mathscr{C}ont_k(Y,Z)\times Y\to Z$ of compactly generated spaces is continuous
-- statement:
--   Continuity of the evaluation map on the product, in the category of compactly generated spaces, of a function space with its source.
--
--   Let $Y,Z$ be compactly generated topological spaces (a subset is open as soon as its preimage under every continuous map from a compact Hausdorff space is open; no separation axiom). Let $\mathscr{C}ont_k(Y,Z)=k(\mathrm{C}(Y,Z))$ be the compactly generated function space: the set of continuous maps $Y\to Z$ with the $k$-ification of the compact-open topology having as sub-base the sets $N(g,K,U)=\{f:(f\circ g)(K)\subseteq U\}$ ($K$ compact Hausdorff, $g:K\to Y$ continuous, $U\subseteq Z$ open). Let $\mathscr{C}ont_k(Y,Z)\times Y:=k\big(\mathscr{C}ont_k(Y,Z)\times_0 Y\big)$ be the product in the category $\mathbf{CG}$ of compactly generated spaces, the $k$-ification of the product topology.
--
--   **Statement.** The evaluation map
--   $$\mathrm{ev}_{Y,Z}:\mathscr{C}ont_k(Y,Z)\times Y\longrightarrow Z,\qquad (f,y)\longmapsto f(y),$$
--   is continuous.
--
--   Equivalently, for every compact Hausdorff space $K$ and all continuous maps $a_1:K\to\mathscr{C}ont_k(Y,Z)$ and $a_2:K\to Y$, the map $t\mapsto a_1(t)(a_2(t))$ is continuous $K\to Z$. The evaluation map is the counit of the adjunction $(-)\times Y\dashv\mathscr{C}ont_k(Y,-)$, i.e. the map corresponding to the identity of $\mathscr{C}ont_k(Y,Z)$ under the exponential law; in general it is not continuous for the product topology $\mathscr{C}ont_k(Y,Z)\times_0Y$. The paper uses it (formula (E.1.2.26)) to prove the exponential law and the cartesian closedness of $\mathbf{CG}$.
--
--   **Formalization Note.** The statement uses the definition file `CGSpace_FunctionSpace`: `CGSpace.ContK Y Z` is $\mathscr{C}ont_k(Y,Z)$ and `CGSpace.KSpace (ContK Y Z × Y)` is the $k$-ification of the product topology; `KSpace.mk.symm` and `ContK.toContinuousMap` are the identity bijections of the type synonyms. Test spaces are compact Hausdorff spaces in the universe `u` of `Y` and `Z` (Mathlib's `CompactlyGeneratedSpace`).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 837-840, Lemma E.1.2.12 ('In particular' clause) and formula (E.1.2.26), proved on pp. 838-839

import Definitions.Def_CGSpace_FunctionSpace

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGSpace

theorem continuous_eval
    (Y Z : Type u) [TopologicalSpace Y] [TopologicalSpace Z]
    [CompactlyGeneratedSpace Y] [CompactlyGeneratedSpace Z] :
    Continuous (fun p : KSpace (ContK Y Z × Y) =>
      ContK.toContinuousMap (KSpace.mk.symm p).1 (KSpace.mk.symm p).2) := by sorry

end CGSpace
