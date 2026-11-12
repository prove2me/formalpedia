-- Prove2me | Theorems.Thm_BunkbedAux_alt_block_sum
-- name    : BunkbedAux.alt_block_sum
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T02:12:48.249383+00:00
-- url     : https://prove2.me/theorems/5276f54d-cb1a-4bb7-860f-a3bfc37c1067
-- title:
--   The all-minus block reproduces Hollom's gap of one
-- statement:
--   In the involution argument for the robustness lemma, after the configurations meeting $\Lambda^2_+$ have cancelled, the dominant contribution comes from the configurations in which **every** hyperedge is fully present on one level and fully absent on the other. There are $2^6 = 64$ of these, one for each level assignment $\sigma$, and each carries weight $W^6$ where $W = P_{abc}P_{a|b|c} - P_{ab|c}P_{ac|b}$.
--
--   This theorem evaluates their net contribution. For each $\sigma$, consider the Wierman--Ziff configuration assigning the fully connecting state $abc$ to hyperedge $i$ on level $\sigma(i)$ and the fully disconnecting state $a|b|c$ on the other level. Then
--
--   $$\sum_{\sigma} \Bigl(\mathbf{1}\bigl[u_1 \leftrightarrow u_{10}'\bigr] - \mathbf{1}\bigl[u_1 \leftrightarrow u_{10}\bigr]\Bigr) \;=\; 1 .$$
--
--   That is, across the $64$ level assignments the cross-level connection occurs exactly one more often than the same-level one.
--
--   The number $1$ is Hollom's $13 - 12$. Indeed these configurations are precisely the *alternative* bunkbed hypergraph percolation model, in which each hyperedge independently picks a level and contributes a triangle there; and Hollom's computation gives $\mathbb{P}^{\mathrm{alt}}[u_1 \leftrightarrow u_{10}] = 12/64$ against $\mathbb{P}^{\mathrm{alt}}[u_1 \leftrightarrow u_{10}'] = 13/64$.
--
--   **Mathematical role.** This is where the refutation actually enters the Wierman--Ziff model. Everything else in the robustness lemma is either an exact cancellation or an error bound; the single unit of asymmetry that makes the final inequality strict is this $1$, inherited from Hollom's hypergraph counterexample. Multiplied by the block weight $W^6$ it is the leading term of the difference of the two connection probabilities, which is why the hypothesis $W > 0$ cannot be dropped: if $W = 0$ the leading term vanishes and, with $P_{a|bc} = 0$ forced by Eq. [1], the two probabilities become exactly equal.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Section 3.6 (p. 6), where conditioning on A reduces the WZ model to the alternative model and Lemma 3.1 supplies 12/64 and 13/64.

import Definitions.Def_BunkbedHypergraph
open Bunkbed Bunkbed.Hyper Finset SimpleGraph

namespace BunkbedAux

/-- **The all-minus block reproduces Hollom's gap.** Summed over the 64 configurations in which
each hyperedge is fully present on one level and fully absent on the other, the net difference
between the cross-level and the same-level connection indicator is exactly `1`, namely Hollom's
`13 - 12`. -/
theorem alt_block_sum :
    (∑ σ : Fin 6 → Fin 2,
        ((if (wzGraph hollomTriple hollomT
              (fun p => if p.2 = σ p.1 then WZ.abc else WZ.a_b_c)).Reachable
            ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) then (1 : ℚ) else 0)
        - (if (wzGraph hollomTriple hollomT
              (fun p => if p.2 = σ p.1 then WZ.abc else WZ.a_b_c)).Reachable
            ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) then (1 : ℚ) else 0))) = 1 := by
  sorry

end BunkbedAux
