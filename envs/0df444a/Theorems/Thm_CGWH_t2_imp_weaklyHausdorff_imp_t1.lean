-- Prove2me | Theorems.Thm_CGWH_t2_imp_weaklyHausdorff_imp_t1
-- name    : CGWH.t2_imp_weaklyHausdorff_imp_t1
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:09.128237+00:00
-- url     : https://prove2.me/theorems/120685b3-4c23-472d-b1cd-0c6243e5fca9
-- title:
--   Hausdorff $\Rightarrow$ weakly Hausdorff $\Rightarrow$ $T_1$
-- statement:
--   The weak Hausdorff separation axiom lies between the Hausdorff axiom $T_2$ and the axiom $T_1$.
--
--   Let $X$ be a topological space. Recall that $X$ is *weakly Hausdorff* if for every compact Hausdorff space $K$ and every continuous map $f:K\to X$ the image $f(K)$ is closed in $X$.
--
--   **Statement.**
--
--   1. If $X$ is Hausdorff, then $X$ is weakly Hausdorff.
--   2. If $X$ is weakly Hausdorff, then $X$ is a $T_1$-space, i.e. every point of $X$ is closed.
--
--   These are the basic comparisons of the weak Hausdorff condition with the classical separation axioms; in particular every locally compact Hausdorff space is compactly generated weakly Hausdorff. Neither implication can be reversed: the paper gives an infinite set with the cofinite topology as a $T_1$-space that is not weakly Hausdorff (Example E.2.1.8) and the one-point compactification of $\mathbf{Q}$ as a compact weakly Hausdorff space that is not Hausdorff (Lemma E.2.4.5).
--
--   **Formalization Note.** The statement is the conjunction of the two implications for one space `X : Type u`. `CGWH.WeaklyHausdorffSpace` is the class of the definition file `CGWH_WeakHausdorff`, whose test spaces are the compact Hausdorff spaces of `Type u`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 846 and 848, Remark E.2.1.3 and Remark E.2.1.7

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGWH

theorem t2_imp_weaklyHausdorff_imp_t1 (X : Type u) [TopologicalSpace X] :
    (T2Space X → WeaklyHausdorffSpace X) ∧ (WeaklyHausdorffSpace X → T1Space X) := by sorry

end CGWH
