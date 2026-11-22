-- Prove2me | Theorems.Thm_CGWH_steenrodCompactlyGeneratedSpace_imp_compactlyGeneratedSpace_and_iff_of_t2
-- name    : CGWH.steenrodCompactlyGeneratedSpace_imp_compactlyGeneratedSpace_and_iff_of_t2
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:24:34.342273+00:00
-- url     : https://prove2.me/theorems/bdfe7f11-2a59-4766-a1a3-634640b8ec1e
-- title:
--   Steenrod compactly generated spaces are compactly generated, and the two notions agree for Hausdorff spaces
-- statement:
--   Comparison of Steenrod compact generation with compact generation.
--
--   Conventions. A topological space $X$ is *compactly generated* if a subset $U\subseteq X$ is open as soon as $g^{-1}(U)$ is open in $K$ for every compact Hausdorff space $K$ and every continuous map $g:K\to X$ (no separation axiom is imposed). It is *Steenrod compactly generated* if a subset $U\subseteq X$ is open as soon as $U\cap K$ is open in $K$ for every compact Hausdorff subspace $K\subseteq X$ (a compact subset which is Hausdorff for the subspace topology). It is *Kelley compactly generated* if a subset $U\subseteq X$ is open as soon as $U\cap K$ is open in $K$ for every compact subspace $K\subseteq X$.
--
--   **Statement.** Let $X$ be a topological space.
--
--   1. If $X$ is Steenrod compactly generated, then $X$ is compactly generated.
--   2. If $X$ is Hausdorff, then $X$ is compactly generated if and only if $X$ is Steenrod compactly generated.
--
--   Mathlib already contains the comparison with the third notion (a compactly generated space is Kelley compactly generated, and a Hausdorff Kelley compactly generated space is compactly generated), so for a Hausdorff space the three notions coincide,
--   $$\text{Kelley compactly generated}\iff\text{compactly generated}\iff\text{Steenrod compactly generated}\qquad(X\text{ Hausdorff}),$$
--   which is the source's Lemma E.2.4.8, while in general
--   $$\text{Steenrod compactly generated}\Longrightarrow\text{compactly generated}\Longrightarrow\text{Kelley compactly generated}$$
--   (the source's Lemma E.2.4.3) and neither implication can be reversed: the Sierpiński space is compactly generated and not Steenrod compactly generated (Lemma E.2.4.7), and the one-point compactification of a non-discrete $T_1$ space with only finite compact subsets is Kelley compactly generated and not compactly generated (Lemma E.2.4.11). The statement justifies that for Hausdorff spaces there is no ambiguity in the literature about the meaning of "compactly generated".
--
--   **Formalization Note.** `CGWH.SteenrodCompactlyGeneratedSpace` is the class of the definition file `CGWH_SteenrodCompactlyGenerated`; `CompactlyGeneratedSpace X`, for `X : Type u`, is Mathlib's notion with test spaces the compact Hausdorff spaces of `Type u`. The theorem is the conjunction of the implication 1 and of the implication "`T2Space X` implies the equivalence 2", with the classes as explicit hypotheses rather than instance arguments.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 865-867, Definition E.2.4.1(2), Lemma E.2.4.3(1) and Lemma E.2.4.8 (equivalence (2) <=> (3))

import Definitions.Def_CGWH_SteenrodCompactlyGenerated

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGWH

theorem steenrodCompactlyGeneratedSpace_imp_compactlyGeneratedSpace_and_iff_of_t2
    (X : Type u) [TopologicalSpace X] :
    (SteenrodCompactlyGeneratedSpace X → CompactlyGeneratedSpace X) ∧
      (T2Space X → (CompactlyGeneratedSpace X ↔ SteenrodCompactlyGeneratedSpace X)) := by sorry

end CGWH
