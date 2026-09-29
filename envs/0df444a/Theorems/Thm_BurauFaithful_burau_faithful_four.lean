-- Prove2me | Theorems.Thm_BurauFaithful_burau_faithful_four
-- name    : BurauFaithful.burau_faithful_four
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T20:15:32.138666+00:00
-- url     : https://prove2.me/theorems/ba582479-b867-4a43-8123-6b2da22bacc9
-- title:
--   The Burau representation $\rho_4$ of $B_4$ is faithful
-- statement:
--   **Main Theorem.** The unreduced Burau representation of the four-strand braid group,
--
--   $$\rho_4 : B_4 \longrightarrow \mathrm{GL}_4(\mathbb{Z}[t,t^{-1}]),$$
--
--   is injective: if two braids on four strands have the same Burau matrix, they are equal; equivalently, the only braid $\Phi \in B_4$ with $\rho_4(\Phi) = I_4$ is the trivial braid.
--
--   Here $B_4$ is Artin's braid group on four strands and $\rho_4$ sends the generator $\sigma_i$ to the identity matrix altered in the rows and columns $i$, $i+1$ by the block $\begin{pmatrix} 1-t & t \\ 1 & 0\end{pmatrix}$.
--
--   This is the last open case of the faithfulness question for the Burau representation: $\rho_3$ is faithful (Magnus–Peluso, 1969) while $\rho_n$ is unfaithful for every $n \ge 5$ (Moody 1991, Long–Paton 1993, Bigelow 1999). Together with the result stated here, $\rho_n$ is faithful exactly for $n \le 4$. An immediate consequence is that the Jones representation of $B_4$ is faithful.
-- source:
--   Vasudha Bharathram, Joan S. Birman, Tara E. Brendle, *The Burau representation is faithful for n = 4*, arXiv:2607.05283v1 (6 July 2026), https://arxiv.org/abs/2607.05283, Main Theorem (p. 1) and Section 6

import Definitions.Def_BurauFaithful_UnreducedBurau

namespace BurauFaithful

theorem burau_faithful_four : Function.Injective (burauRep 4) := by sorry

end BurauFaithful
