-- Prove2me | Theorems.Thm_BunkbedAux_A_block_value
-- name    : BunkbedAux.A_block_value
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T02:59:32.38965+00:00
-- url     : https://prove2.me/theorems/ac9e71c6-bdfa-4e75-b2c9-b568a0230d7f
-- title:
--   The all-minus block contributes exactly $W^6$
-- statement:
--   In the involution argument, after the configurations meeting $\Lambda^2_+$ have cancelled, the leading contribution comes from the configurations in which every hyperedge is in a $-$ state, that is, fully present on one level and fully absent on the other. This theorem evaluates that contribution exactly.
--
--   Writing $W = P_{abc}P_{a|b|c} - P_{ab|c}P_{ac|b}$, the claim is
--
--   $$\sum_{\Psi \in A} \mathrm{wt}(\Psi)\Bigl(\mathbf{1}\bigl[u_1 \leftrightarrow u_{10}'\bigr] - \mathbf{1}\bigl[u_1 \leftrightarrow u_{10}\bigr]\Bigr) \;=\; W^{6},$$
--
--   where $A$ is the set of configurations all of whose hyperedges are in a $-$ state.
--
--   Two things combine to give this. Each of the $2^6 = 64$ configurations in $A$ carries weight exactly $W^6$, since each $-$ variant has weight $W$. And $A$ is in bijection with the level assignments $\sigma$, under which the realised graph is exactly the alternative-model graph at $\sigma$; so the net indicator difference summed over $A$ is the alternative model's surplus, which by Hollom's computation is $13 - 12 = 1$.
--
--   **Mathematical role.** This is the term that makes the robustness lemma true. Everything else in the argument is either an exact cancellation or an error bound: the configurations meeting $\Lambda^2_+$ contribute zero, and the remaining ones are controlled in absolute value by their total weight. The single positive term is this $W^6$, and it is positive precisely under the hypothesis $W > 0$ — which is why that hypothesis cannot be dropped. Under Eq. [1] the error is at most $Z^6 - 64W^6$ with $Z = 2W + 2P_{a|bc} - P_{a|bc}^2$, and $W^6$ dominates it because $64 \cdot 401^6 < 65 \cdot 400^6$.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Section 3.6 (p. 6): conditioning on A and applying Lemma 3.1.

import Definitions.Def_BunkbedWZSurgery
open Bunkbed Bunkbed.Hyper Finset SimpleGraph

namespace BunkbedAux

/-- **The all-minus block contributes exactly `W ^ 6`.** Summed over the refined configurations
in which every hyperedge is in a `-` state, the weight times the net indicator difference is
`W ^ 6`, where `W = P_abc * P_a|b|c - P_ab|c * P_ac|b`. -/
theorem A_block_value (P : WZ → ℚ) :
    ∑ Ψ ∈ Finset.univ.filter (fun Ψ : Fin 6 → WZExt =>
        ∀ h, Ψ h ∈ ({Sum.inr 1, Sum.inr 3} : Finset WZExt)),
        (∏ h, WZExt.wt P (Ψ h)) *
          ((if (wzGraph hollomTriple hollomT (wzOfExt Ψ)).Reachable
              ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) then (1 : ℚ) else 0)
          - (if (wzGraph hollomTriple hollomT (wzOfExt Ψ)).Reachable
              ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) then (1 : ℚ) else 0))
      = (P .abc * P .a_b_c - P .ab_c * P .ac_b) ^ 6 := by
  sorry

end BunkbedAux
