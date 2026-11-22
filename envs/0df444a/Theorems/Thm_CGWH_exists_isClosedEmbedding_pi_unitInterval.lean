-- Prove2me | Theorems.Thm_CGWH_exists_isClosedEmbedding_pi_unitInterval
-- name    : CGWH.exists_isClosedEmbedding_pi_unitInterval
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:31:50.297801+00:00
-- url     : https://prove2.me/theorems/c3e91668-0601-4448-8cc5-87d4e71eaa58
-- title:
--   A compact Hausdorff space $K$ with $|C(K,\mathbf{C})|\le\kappa$ embeds as a closed subspace of the cube $[0,1]^{\kappa}$
-- statement:
--   Tychonoff's embedding of a compact Hausdorff space into a cube, with a bound on the number of coordinates in terms of the cardinality of the algebra of continuous functions.
--
--   Let $K$ be a compact Hausdorff topological space and let $C(K)=C(K,\mathbf{C})$ be the set of continuous complex-valued functions on $K$. For a set $\iota$ let $[0,1]^{\iota}=\prod_{\iota}[0,1]$ be the product of copies of the unit interval indexed by $\iota$, with the product topology.
--
--   **Statement.** If $\iota$ is a set of cardinality $\kappa$ with $$|C(K,\mathbf{C})|\le\kappa,$$ then there exists a closed embedding (a homeomorphism onto a closed subspace) $$\varphi:K\longrightarrow\prod_{\iota}[0,1]=[0,1]^{\kappa}.$$
--
--   Consequently, for every cardinal $\kappa$, every compact Hausdorff space $K$ with $|C(K)|\le\kappa$ is homeomorphic to a closed subspace of the single cube $[0,1]^{\kappa}$, so these spaces form only a set of homeomorphism classes. The paper uses this to build a small category of compactly generated weakly Hausdorff spaces closed under the operations it needs.
--
--   **Formalization Note.** `K : Type u`, `ι : Type v`; the hypothesis compares `Cardinal.mk C(K, ℂ)` and `Cardinal.mk ι` after lifting both to the universe `max u v`. `unitInterval` is Mathlib's $[0,1]$ and `ι → unitInterval` carries the product topology. **Deviation from the source.** The paper assumes $\mathrm{size}(K)\le\kappa$, where $\mathrm{size}(K)$ is the maximum of $\aleph_0$, the number of compact Hausdorff subspaces of $K$ and the supremum of $|C(K',\mathbf{C})|$ over those subspaces $K'$ (Definition E.3.1.1); since $K$ is one of these subspaces this implies $|C(K,\mathbf{C})|\le\kappa$, which is the only consequence used in the proof and is the hypothesis stated here. The paper recalls the lemma as a well-known result on compact Hausdorff spaces without a reference.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 871, Lemma E.3.1.5

import Mathlib

open Topology TopologicalSpace

set_option autoImplicit false

universe u v

namespace CGWH

theorem exists_isClosedEmbedding_pi_unitInterval
    {K : Type u} {ι : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (h : Cardinal.lift.{v} (Cardinal.mk C(K, ℂ)) ≤ Cardinal.lift.{u} (Cardinal.mk ι)) :
    ∃ φ : K → (ι → unitInterval), IsClosedEmbedding φ := by sorry

end CGWH
