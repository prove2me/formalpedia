-- Prove2me | Theorems.Thm_BunkbedAux_xc_and_A_weight
-- name    : BunkbedAux.xc_and_A_weight
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T02:18:13.244702+00:00
-- url     : https://prove2.me/theorems/5df54d2b-7543-416d-940c-b2eceb96bd2f
-- title:
--   The weights of the two blocks outside $\Lambda^2_+$
-- statement:
--   Once the configurations meeting $\Lambda^2_+$ have been cancelled by the involution, the robustness lemma reduces to the complementary set: those in which *every* hyperedge avoids $\Lambda^2_+$. This theorem computes the total weight of that set, and of the sub-block that carries the refutation.
--
--   Write $W = P_{abc}P_{a|b|c} - P_{ab|c}P_{ac|b}$ and let $P$ be a probability distribution on the five Wierman--Ziff states. Then:
--
--   1. the configurations all of whose hyperedges avoid $\Lambda^2_+$ have total weight
--   $$Z^{6}, \qquad Z = 2W + 2P_{a|bc} - P_{a|bc}^{2};$$
--   2. the configurations all of whose hyperedges are in a $-$ state have total weight
--   $$(2W)^{6} = 64\,W^{6}.$$
--
--   Both follow from the per-hyperedge weights by independence across hyperedges: a set of configurations specified by a condition on each coordinate separately is a product, so its total weight is the product of the per-coordinate weights, and here that product is a sixth power since the condition is the same at every hyperedge. The per-hyperedge figure $Z$ counts the two $-$ variants, of weight $W$ each, together with the nine pairs involving the state $a|bc$, whose weight is $2P_{a|bc} - P_{a|bc}^2$ by inclusion--exclusion; the normalisation $\sum_s P_s = 1$ is used exactly there.
--
--   **Mathematical role.** The ratio of the two is the conditional probability that every hyperedge is in a $-$ state, given that all avoid $\Lambda^2_+$. Those $2^6 = 64$ all-minus configurations are precisely the alternative bunkbed hypergraph model, and by Hollom's computation they contribute a net surplus of one cross-level connection — the source of the refutation. All other configurations in the complement are error terms, bounded in absolute value by their total weight $Z^6 - (2W)^6$. Under Eq. [1], which reads $400P_{a|bc} \le W$, one has $Z \le 2W \cdot \frac{401}{400}$, and the refutation survives because
--   $$64 \cdot 401^{6} \;<\; 65 \cdot 400^{6},$$
--   which is exactly the inequality $Z^6 < 65\,W^6$ needed for the surplus $W^6$ to dominate the error $Z^6 - 64W^6$. The margin is about one part in two thousand, which is why the constant in Eq. [1] has to be as large as it is.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Section 3.6 (p. 6): the normalizing constant Z and the event A.

import Definitions.Def_BunkbedWZRefined
open Bunkbed Bunkbed.Hyper Finset

namespace BunkbedAux

/-- **The weights of the two blocks outside `Λ²₊`.** The configurations all of whose hyperedges
avoid `Λ²₊` have total weight `Z ^ 6` with `Z = 2W + 2 P_a|bc - P_a|bc ^ 2`, and those all of
whose hyperedges are in a `-` state have total weight `(2W) ^ 6`, where
`W = P_abc * P_a|b|c - P_ab|c * P_ac|b`. -/
theorem xc_and_A_weight (P : WZ → ℚ)
    (hsum : P .abc + P .a_b_c + P .a_bc + P .ab_c + P .ac_b = 1) :
    (∑ Ψ ∈ Finset.univ.filter (fun Ψ : Fin 6 → WZExt =>
        ∀ h, Ψ h ∈ Finset.univ.filter
          (fun q : WZExt => WZExt.legal q = true ∧ WZExt.inLamSq q = false)),
        ∏ h, WZExt.wt P (Ψ h))
      = (2 * (P .abc * P .a_b_c - P .ab_c * P .ac_b) + 2 * P .a_bc - P .a_bc * P .a_bc) ^ 6
    ∧ (∑ Ψ ∈ Finset.univ.filter (fun Ψ : Fin 6 → WZExt =>
        ∀ h, Ψ h ∈ ({Sum.inr 1, Sum.inr 3} : Finset WZExt)), ∏ h, WZExt.wt P (Ψ h))
      = (2 * (P .abc * P .a_b_c - P .ab_c * P .ac_b)) ^ 6 := by
  sorry

end BunkbedAux
