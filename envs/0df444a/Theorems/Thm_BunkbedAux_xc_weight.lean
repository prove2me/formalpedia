-- Prove2me | Theorems.Thm_BunkbedAux_xc_weight
-- name    : BunkbedAux.xc_weight
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T01:26:44.081821+00:00
-- url     : https://prove2.me/theorems/e5f9c13a-57f9-42ab-ade7-1f035d4e0cab
-- title:
--   The weight of the complement of $\Lambda^2_+$
-- statement:
--   In the involution argument of Gladkov--Pak--Zimin, the configurations meeting $\Lambda^2_+$ cancel between the two connection events, and what remains is the complementary set $X^c$: the configurations in which *every* hyperedge avoids $\Lambda^2_+$. This theorem computes the per-hyperedge weight of that complement, which is the normalizing constant of the conditional measure on $X^c$.
--
--   Write $W = P_{abc}P_{a|b|c} - P_{ab|c}P_{ac|b}$ for the determinant-like quantity of Eq. [1], and let $P$ be a probability distribution on the five Wierman--Ziff states, so $P_{abc} + P_{a|b|c} + P_{a|bc} + P_{ab|c} + P_{ac|b} = 1$. Then the total weight of the legal refined states of a single hyperedge lying outside $\Lambda^2_+$ is
--
--   $$Z \;=\; 2W \;+\; 2P_{a|bc} \;-\; P_{a|bc}^{2},$$
--
--   and the two $-$ variants alone contribute $2W$.
--
--   **Where the two terms come from.** Of the $27$ legal refined states, $16$ lie in $\Lambda^2_+$, leaving $11$. Two of these are the $-$ variants of the split pairs, each of weight $W$, giving $2W$; these are exactly the configurations in which the hyperedge is fully present on one level and fully absent on the other. The other nine are the pairs having the state $a|bc$ in at least one coordinate: five of the form $(a|bc, \beta)$, five of the form $(\alpha, a|bc)$, with the pair $(a|bc,a|bc)$ counted in both. Their total weight is
--   $$P_{a|bc}\sum_\beta P_\beta \;+\; \Bigl(\sum_\alpha P_\alpha\Bigr)P_{a|bc} \;-\; P_{a|bc}^2 \;=\; 2P_{a|bc} - P_{a|bc}^2,$$
--   using that $P$ sums to $1$. This is the only place the normalisation hypothesis is needed.
--
--   **Mathematical role.** The ratio $2W/Z$ is the conditional probability, given $X^c$, that a single hyperedge is in a $-$ state; raised to the sixth power it is the probability of the event $A$ that *all* hyperedges are, and conditioned on $A$ the Wierman--Ziff model reduces to the alternative bunkbed hypergraph model, where Hollom's computation applies. The hypothesis Eq. [1], $400P_{a|bc} \le W$, enters precisely here: it forces $2P_{a|bc} - P_{a|bc}^2$ to be small compared with $2W$, hence $A$ to have probability close to one, and the sign of the difference is then inherited from Hollom's $12/64$ versus $13/64$.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Section 3.6 (p. 6): the list of pairs in Upsilon^2_ext minus Lambda^2_+ and the normalizing constant Z.

import Definitions.Def_BunkbedWZRefined
open Bunkbed.Hyper Finset

namespace BunkbedAux

/-- **The weight of the complement of `Λ²₊`.** Summed over the legal refined states of a single
hyperedge that do *not* lie in `Λ²₊`, the weight is the normalizing constant
`Z = 2W + 2 P_a|bc - P_a|bc ^ 2` of Gladkov-Pak-Zimin, where
`W = P_abc * P_a|b|c - P_ab|c * P_ac|b`; and the two `-` variants alone contribute `2W`. -/
theorem xc_weight (P : WZ → ℚ)
    (hsum : P .abc + P .a_b_c + P .a_bc + P .ab_c + P .ac_b = 1) :
    (∑ q ∈ Finset.univ.filter
        (fun q : WZExt => WZExt.legal q = true ∧ WZExt.inLamSq q = false), WZExt.wt P q)
      = 2 * (P .abc * P .a_b_c - P .ab_c * P .ac_b) + 2 * P .a_bc - P .a_bc * P .a_bc
    ∧ (WZExt.wt P (Sum.inr 1) + WZExt.wt P (Sum.inr 3))
      = 2 * (P .abc * P .a_b_c - P .ab_c * P .ac_b) := by
  sorry

end BunkbedAux
