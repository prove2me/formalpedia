-- Prove2me | Theorems.Thm_CGWH_t2Space_of_surjective_of_compactSpace_t2Space
-- name    : CGWH.t2Space_of_surjective_of_compactSpace_t2Space
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:05.702628+00:00
-- url     : https://prove2.me/theorems/5b304dc1-a0e4-405d-91a9-deb5b9a69c5f
-- title:
--   A weakly Hausdorff continuous image of a compact Hausdorff space is Hausdorff
-- statement:
--   A weakly Hausdorff space that is a continuous image of a compact Hausdorff space is Hausdorff.
--
--   Recall that a topological space $X$ is *weakly Hausdorff* if for every compact Hausdorff space $C$ and every continuous map $f:C\to X$ the image $f(C)$ is closed in $X$.
--
--   **Statement.** Let $K$ be a weakly Hausdorff topological space, let $K'$ be a compact Hausdorff topological space and let $q:K'\to K$ be a continuous surjective map. Then $K$ is a Hausdorff space (and it is compact, being the image of $K'$).
--
--   Since subspaces of weakly Hausdorff spaces are weakly Hausdorff, the statement applies to the image of any test map: if $X$ is weakly Hausdorff, $K'$ is compact Hausdorff and $f:K'\to X$ is continuous, then $f(K')$ is a closed, compact *Hausdorff* subspace of $X$. This is the basic tool of the theory of compactly generated weakly Hausdorff spaces: it is the first step in proving that the diagonal of a weakly Hausdorff space is $k$-closed (the paper's Lemma E.2.1.6), and it shows that the test spaces of a compactly generated weakly Hausdorff space can be taken to be its closed compact Hausdorff subspaces (Proposition E.2.1.13).
--
--   **Formalization Note.** The source also assumes that $K$ is compact; this is automatic, because $K=q(K')$, so the hypothesis is not repeated. `K` and `K'` live in the same universe `u`, the universe of the test spaces of `CGWH.WeaklyHausdorffSpace K` (definition file `CGWH_WeakHausdorff`).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 846, Lemma E.2.1.4

import Definitions.Def_CGWH_WeakHausdorff

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace CGWH

theorem t2Space_of_surjective_of_compactSpace_t2Space
    {K K' : Type u} [TopologicalSpace K] [WeaklyHausdorffSpace K]
    [TopologicalSpace K'] [CompactSpace K'] [T2Space K']
    {q : K' → K} (hq : Continuous q) (hs : Function.Surjective q) : T2Space K := by sorry

end CGWH
