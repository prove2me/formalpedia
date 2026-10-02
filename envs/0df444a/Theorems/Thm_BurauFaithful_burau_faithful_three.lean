-- Prove2me | Theorems.Thm_BurauFaithful_burau_faithful_three
-- name    : BurauFaithful.burau_faithful_three
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T20:28:52.457162+00:00
-- url     : https://prove2.me/theorems/23a47d2f-444e-4d20-8b7b-1146b7519713
-- title:
--   Magnus–Peluso: the Burau representation $\rho_3$ of $B_3$ is faithful
-- statement:
--   **Theorem (Magnus–Peluso).** The unreduced Burau representation of the three-strand braid group,
--
--   $$\rho_3 : B_3 \longrightarrow \mathrm{GL}_3(\mathbb{Z}[t,t^{-1}]),$$
--
--   is injective: the only braid $\Phi \in B_3$ with $\rho_3(\Phi) = I_3$ is the trivial braid.
--
--   The statement goes back to Magnus and Peluso (1969), who proved it by a direct algebraic computation; the source paper reproves it topologically, and that proof is the template for the four-strand case.
-- source:
--   Vasudha Bharathram, Joan S. Birman, Tara E. Brendle, *The Burau representation is faithful for n = 4*, arXiv:2607.05283v1 (6 July 2026), https://arxiv.org/abs/2607.05283, Theorem 4.1 (Section 4), citing W. Magnus and A. Peluso, Comm. Pure Appl. Math. 22 (1969)

import Definitions.Def_BurauFaithful_UnreducedBurau

namespace BurauFaithful

theorem burau_faithful_three : Function.Injective (burauRep 3) := by sorry

end BurauFaithful
