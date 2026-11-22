-- Prove2me | Theorems.Thm_CGWH_onePoint_rat_weaklyHausdorff_not_t2
-- name    : CGWH.onePoint_rat_weaklyHausdorff_not_t2
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:36.384619+00:00
-- url     : https://prove2.me/theorems/da8681a3-84b3-4d1c-b9a0-d2259691235c
-- title:
--   $\mathbf{Q}^+$ is compact, compactly generated and weakly Hausdorff but not Hausdorff, and $\mathbf{Q}^+\times_0\mathbf{Q}^+$ is not compactly generated
-- statement:
--   The one-point compactification of the rational numbers: a compact, compactly generated, weakly Hausdorff space that is not Hausdorff and whose square is not compactly generated.
--
--   Let $\mathbf{Q}$ carry the topology induced from $\mathbf{R}$ and let $\mathbf{Q}^+=\mathbf{Q}\cup\{\infty\}$ be its one-point compactification: the open sets are the open subsets of $\mathbf{Q}$ and the complements in $\mathbf{Q}^+$ of the closed compact subsets of $\mathbf{Q}$. It is a compact space. A space $X$ is *compactly generated* if a subset is open as soon as its preimage under every continuous map from a compact Hausdorff space to $X$ is open, and *weakly Hausdorff* if the image of every such map is closed in $X$.
--
--   **Statement.**
--
--   1. $\mathbf{Q}^+$ is compactly generated.
--   2. $\mathbf{Q}^+$ is weakly Hausdorff.
--   3. $\mathbf{Q}^+$ is not Hausdorff.
--   4. The product $\mathbf{Q}^+\times_0\mathbf{Q}^+$, with the product topology, is not compactly generated.
--
--   Thus the weak Hausdorff condition is strictly weaker than the Hausdorff condition even for compact compactly generated spaces, the hypothesis "continuous image of a compact Hausdorff space" cannot be dropped in the theorem that such weakly Hausdorff spaces are Hausdorff, and the product, with the product topology, of a compactly generated space and a compact weakly Hausdorff space need not be compactly generated, in contrast with the case of a locally compact Hausdorff factor. Since $\mathbf{Q}^+$ is weakly Hausdorff and compactly generated, its diagonal is closed in $k(\mathbf{Q}^+\times_0\mathbf{Q}^+)$ but not in $\mathbf{Q}^+\times_0\mathbf{Q}^+$: the topological diagonal of a compactly generated weakly Hausdorff space need not be closed.
--
--   **Formalization Note.** $\mathbf{Q}^+$ is Mathlib's `OnePoint ℚ`, a compact space by a Mathlib instance. `CompactlyGeneratedSpace` (Mathlib) and `CGWH.WeaklyHausdorffSpace` (definition file `CGWH_WeakHausdorff`) are taken in universe `0`, the universe of `OnePoint ℚ`: the test spaces are the compact Hausdorff spaces of `Type`. `OnePoint ℚ × OnePoint ℚ` carries the product topology.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 866-867, Example E.2.4.4, Lemma E.2.4.5 and Lemma E.2.4.9; classical reference (as cited by the paper for this space): L. A. Steen, J. A. Seebach, Jr., Counterexamples in Topology, 2nd ed., Springer-Verlag (1978), Part II, 35

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

namespace CGWH

theorem onePoint_rat_weaklyHausdorff_not_t2 :
    CompactlyGeneratedSpace (OnePoint ℚ) ∧ WeaklyHausdorffSpace (OnePoint ℚ) ∧
      ¬ T2Space (OnePoint ℚ) ∧ ¬ CompactlyGeneratedSpace (OnePoint ℚ × OnePoint ℚ) := by sorry

end CGWH
