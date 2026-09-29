-- Prove2me | Theorems.Thm_BurauFaithful_b5_parity_obstruction
-- name    : BurauFaithful.b5_parity_obstruction
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-24T12:53:07.832493+00:00
-- url     : https://prove2.me/theorems/d2b5ab27-f9ff-4e06-9b5d-29088118ed95
-- title:
--   B5 parity correction for proper products of push-maps in K4
-- statement:
--   **Proposition 6.4 / Corollary 6.5 of Bharathram–Birman–Brendle.** Let $K_4$ be the point-pushing subgroup of $B_4$ and $\Gamma_1 \in K_4$ the push-map along the simple loop of Figure 6.3. If $\Phi \in K_4$ is a proper product $\Phi = \Phi' \cdot \Gamma_1$ (with $\Phi' \in K_4$), then $\Phi$ does not lie in the kernel of the Burau representation $\rho_4$. The proof (Section 6.3): the only disk type in the disk sequence of $\Phi$ violating the parity condition is a 4-disk; embedding $D_4 \hookrightarrow D_5$ and pushing the 5th point along a suitable loop $\Gamma \in K_5$ replaces every 4-disk by a sign-changing 5-disk, so that both $f(\Phi) \cdot \Gamma$ and $\Gamma$ satisfy the parity condition (Proposition 6.4). The Moody polynomials then satisfy $\mathbb{M}_{f(\Phi)\cdot\Gamma} \neq \mathbb{M}_{\Gamma}$ (Corollary 6.5), so Moody's theorem (Theorem 2.3) gives $f(\Phi) \notin \ker \rho_5$, and Observation 2.1 (`BurauFaithful.burau_ker_le_ker_succ`, proved) lifts this to $\Phi \notin \ker \rho_4$. This is the key step feeding Theorem 6.6 (`BurauFaithful.burau_faithful_on_brun4`). Reference: arXiv:2607.05283v2 (14 Sep 2026), Proposition 6.4, Corollary 6.5, Section 6.3.
-- source:
--   Vasudha Bharathram, Joan S. Birman, Tara E. Brendle, *The Burau representation of the braid group is faithful for n = 4*, arXiv:2607.05283v2 (14 Sep 2026), https://arxiv.org/abs/2607.05283, Proposition 6.4, Corollary 6.5, Section 6.3 (B5 parity correction)

import Definitions.Def_BurauFaithful_UnreducedBurau
import Definitions.Def_BurauFaithful_StandardInclusion
set_option autoImplicit false

namespace BurauFaithful

theorem b5_parity_obstruction (K4 : Subgroup (BraidsLinksMCG.ArtinBraidGroup 4))
    (gamma1 : BraidsLinksMCG.ArtinBraidGroup 4) (hgamma1 : gamma1 ∈ K4)
    (Phi Phi' : BraidsLinksMCG.ArtinBraidGroup 4)
    (hPhi' : Phi' ∈ K4) (hPhi : Phi ∈ K4) (hprod : Phi = Phi' * gamma1) :
    burauRep 4 Phi ≠ 1 := by sorry

end BurauFaithful
