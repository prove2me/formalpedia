-- Prove2me | Theorems.Thm_BunkbedAux_xc_block_pos
-- name    : BunkbedAux.xc_block_pos
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T03:16:38.710876+00:00
-- url     : https://prove2.me/theorems/391fd055-d4ab-4adb-bdf3-87443a16eaac
-- title:
--   The complement of $\Lambda^2_+$ contributes strictly positively
-- statement:
--   After the involution has cancelled every configuration meeting $\Lambda^2_+$, the robustness lemma comes down to the complementary configurations — those in which every hyperedge avoids $\Lambda^2_+$. This theorem shows that block contributes a strictly positive amount, which is the whole of the inequality.
--
--   Let $P$ be a probability distribution on the five Wierman--Ziff states, put $W = P_{abc}P_{a|b|c} - P_{ab|c}P_{ac|b}$, and assume $W > 0$ together with Eq. [1],
--   $$400\,P_{a|bc} \;\le\; W .$$
--   Then the weighted net difference between the cross-level and the same-level connection indicator, summed over the complement, is strictly positive.
--
--   **How the sign is obtained.** The complement splits in two. The sub-block in which every hyperedge is in a $-$ state — fully present on one level, fully absent on the other — is exactly the alternative bunkbed hypergraph model, and it contributes precisely $W^6$: each of its $64$ configurations has weight $W^6$, and their net indicator surplus is Hollom's $13 - 12 = 1$. Everything else in the complement is an error term, bounded in absolute value by its total weight, since each indicator difference lies in $\{-1, 0, 1\}$ and all weights are nonnegative.
--
--   The two weights are $Z^6$ for the whole complement and $(2W)^6 = 64W^6$ for the $-$ block, where $Z = 2W + 2P_{a|bc} - P_{a|bc}^2$. So positivity amounts to
--   $$W^{6} \;>\; Z^{6} - 64\,W^{6}, \qquad\text{that is}\qquad Z^{6} < 65\,W^{6}.$$
--   Eq. [1] gives $2P_{a|bc} - P_{a|bc}^2 \le 2P_{a|bc} \le W/200$, hence $Z \le W \cdot \tfrac{401}{200}$, and the requirement reduces to the numerical fact
--   $$401^{6} \;<\; 65 \cdot 200^{6},$$
--   i.e. $4157825282402401 < 4160000000000000$.
--
--   **On the constant.** The margin is about one part in two thousand. This is why Eq. [1] needs a constant as large as it does: by this route any constant below $387$ fails. It is also why the hypothesis $W > 0$ is indispensable — it is exactly the positivity of the leading term $W^6$, and when $W = 0$ the whole expression vanishes.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Section 3.6 (pp. 6): the bound on P_{X^c}(A) and the final combination.

import Definitions.Def_BunkbedWZSurgery
open Bunkbed Bunkbed.Hyper Finset SimpleGraph

namespace BunkbedAux

/-- **The complement of `Λ²₊` contributes a strictly positive amount.** Under Eq. [1] together
with `0 < W`, the weighted net indicator difference over the configurations all of whose
hyperedges avoid `Λ²₊` is strictly positive. -/
theorem xc_block_pos (P : WZ → ℚ)
    (hnn : ∀ s, 0 ≤ P s)
    (hsum : P .abc + P .a_b_c + P .a_bc + P .ab_c + P .ac_b = 1)
    (hpos : 0 < P .abc * P .a_b_c - P .ab_c * P .ac_b)
    (h400 : 400 * P .a_bc ≤ P .abc * P .a_b_c - P .ab_c * P .ac_b) :
    0 < ∑ Ψ ∈ Finset.univ.filter (fun Ψ : Fin 6 → WZExt =>
        ∀ h, Ψ h ∈ Finset.univ.filter
          (fun q : WZExt => WZExt.legal q = true ∧ WZExt.inLamSq q = false)),
        (∏ h, WZExt.wt P (Ψ h)) *
          ((if (wzGraph hollomTriple hollomT (wzOfExt Ψ)).Reachable
              ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) then (1 : ℚ) else 0)
          - (if (wzGraph hollomTriple hollomT (wzOfExt Ψ)).Reachable
              ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) then (1 : ℚ) else 0)) := by
  sorry

end BunkbedAux
