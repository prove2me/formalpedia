-- Prove2me | Theorems.Thm_BurauFaithful_burau_ker_le_ker_succ
-- name    : BurauFaithful.burau_ker_le_ker_succ
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T20:32:45.439649+00:00
-- url     : https://prove2.me/theorems/3aed5109-4333-4dde-95ff-7f1d18fbc1da
-- title:
--   Kernels of Burau under the standard inclusion $B_n \hookrightarrow B_{n+1}$
-- statement:
--   **Observation.** Let $n$ be a natural number and let $\iota : B_n \to B_{n+1}$ be the standard inclusion, induced by the embedding of the $n$-punctured disk into the $(n+1)$-punctured disk and sending each Artin generator to the generator of the same index. If a braid $\Phi \in B_n$ lies in the kernel of the Burau representation, that is
--
--   $$\rho_n(\Phi) = I_n,$$
--
--   then its image lies in the kernel of the Burau representation one strand up:
--
--   $$\rho_{n+1}(\iota(\Phi)) = I_{n+1}.$$
--
--   In other words, $\iota(\ker \rho_n) \subseteq \ker \rho_{n+1}$: adding an unbraided strand cannot detect a braid that Burau does not already detect. The statement holds for every $n$, including the degenerate cases $n \le 1$ where the braid group is trivial. It is used in the source paper to move a four-strand braid into $B_5$, where a parity obstruction becomes available.
-- source:
--   Vasudha Bharathram, Joan S. Birman, Tara E. Brendle, *The Burau representation is faithful for n = 4*, arXiv:2607.05283v1 (6 July 2026), https://arxiv.org/abs/2607.05283, Observation 2.1 (Section 2, p. 3)

import Definitions.Def_BurauFaithful_UnreducedBurau
import Definitions.Def_BurauFaithful_StandardInclusion

namespace BurauFaithful

theorem burau_ker_le_ker_succ (n : ℕ) (Φ : BraidsLinksMCG.ArtinBraidGroup n)
    (h : burauRep n Φ = 1) : burauRep (n + 1) (standardInclusion n Φ) = 1 := by sorry

end BurauFaithful
