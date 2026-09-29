-- Prove2me | Theorems.Thm_BurauFaithful_burau_faithful_on_brun4
-- name    : BurauFaithful.burau_faithful_on_brun4
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-24T12:52:43.499223+00:00
-- url     : https://prove2.me/theorems/f536d4d8-b4a7-4fc4-bf77-794986f2165f
-- title:
--   Burau representation rho4 is faithful on the Brunnian subgroup
-- statement:
--   **Theorem 6.6 of Bharathram–Birman–Brendle.** The unreduced Burau representation $\rho_4 : B_4 \to \mathrm{GL}_4(\mathbb{Z}[t,t^{-1}])$ is faithful on its restriction to the Brunnian subgroup $\mathrm{Brun}_4$ of $B_4$. Here $\mathrm{Brun}_4 = \bigcap_{i=1}^4 K_i$ is the intersection of the four point-pushing subgroups of $B_4$ (kernels of the Birman exact-sequence forget maps); the paper proves (Section 1) that $\mathrm{Brun}_4$ is a normal, nontrivial, noncentral subgroup of $B_4$ — the hypotheses carried by the formal statement. Every nontrivial $\Phi \in \mathrm{Brun}_4$ is pseudo-Anosov (Whittlesey), hence after conjugation lies in $K_4$ as a proper product of push-maps; the proof then applies the B5 parity-correction argument (Proposition 6.4 / Corollary 6.5) to show $\Phi \notin \ker \rho_4$. Combined with Long's criterion (`BurauFaithful.burau_faithful_of_faithful_on_normal`, node 906aaa4a-93c6-4fbf-862e-71e93ea21242), this node implies the Main Theorem `BurauFaithful.burau_faithful_four`. Reference: arXiv:2607.05283v2 (14 Sep 2026), Theorem 6.6, Section 6.4.
-- source:
--   Vasudha Bharathram, Joan S. Birman, Tara E. Brendle, *The Burau representation of the braid group is faithful for n = 4*, arXiv:2607.05283v2 (14 Sep 2026), https://arxiv.org/abs/2607.05283, Theorem 6.6 and Section 6.4 (faithfulness on Brun_4)

import Definitions.Def_BurauFaithful_UnreducedBurau
set_option autoImplicit false

namespace BurauFaithful

theorem burau_faithful_on_brun4 (Brun4 : Subgroup (BraidsLinksMCG.ArtinBraidGroup 4))
    [Brun4.Normal] (hnontrivial : Brun4 ≠ ⊥)
    (hnoncentral : ¬ Brun4 ≤ Subgroup.center (BraidsLinksMCG.ArtinBraidGroup 4)) :
    ∀ x ∈ Brun4, burauRep 4 x = 1 → x = 1 := by sorry

end BurauFaithful
