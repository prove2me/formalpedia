-- Prove2me | Theorems.Thm_BunkbedFalse_gadget_eq1_at_half
-- name    : BunkbedFalse.gadget_eq1_at_half
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T03:33:55.292915+00:00
-- url     : https://prove2.me/theorems/ae4b8662-068e-4ccd-9982-45d854fb7f81
-- title:
--   The gadget at $P=1/2$, $n=1204$ satisfies Eq. [1]
-- statement:
--   Section 4.2 of Gladkov--Pak--Zimin takes $P = 1/2$ and $n = 3 \cdot 401 + 1 = 1204$ and asserts that "the $\tfrac12$-percolation on $G_n$ satisfies conditions of Lemma 3.3". This theorem is that assertion.
--
--   For the gadget $G_{1204}$ under $\tfrac12$-percolation, with the distinguished triple $a = 0$, $b = v_1$, $c = v_{1204}$, the five partition probabilities satisfy all three conditions required by the robustness lemma:
--
--   1. the symmetry $P_{ab|c} = P_{ac|b}$;
--   2. strict positivity of the determinant, $P_{abc}P_{a|b|c} - P_{ab|c}P_{ac|b} > 0$;
--   3. Eq. [1], namely $400\,P_{a|bc} \le P_{abc}P_{a|b|c} - P_{ab|c}P_{ac|b}$.
--
--   **Where the constant comes from.** The hyperedge-simulation lemma gives, for $n \ge 3$ and $0 < P < 1$, the strict bound
--   $$P_{abc}P_{a|b|c} - P_{ab|c}P_{ac|b} \;>\; \Bigl(\frac{n(1-P)}{1+P} - 1\Bigr) P_{a|bc},$$
--   and at $P = 1/2$, $n = 1204$ the bracket is
--   $$\frac{1204 \cdot \tfrac12}{\tfrac32} - 1 \;=\; \frac{1204}{3} - 1 \;=\; \frac{1201}{3} \;=\; 400.333\ldots,$$
--   comfortably above $400$. This is exactly why the source chooses $n = 3 \cdot 401 + 1$: the bracket is $\tfrac{n}{3} - 1$ at $P = 1/2$, so $n = 1204$ is the smallest value of that form clearing $400$.
--
--   Positivity of the determinant is a separate matter and follows because $P_{a|bc} = P^{2n-1} = 2^{-2407}$ is strictly positive, so the strict bound above already forces the determinant to exceed a positive quantity.
--
--   **Mathematical role.** This is the hinge between Sections 4 and 3 of the source. The robustness lemma says that any hyperedge whose partition probabilities satisfy these conditions can be substituted into Hollom's hypergraph while preserving the strict reversal of the bunkbed inequality; this theorem verifies the conditions for the concrete gadget used in Theorem 1.2. Note in particular that condition 2 is the hypothesis which this mission's statement of the robustness lemma adds to the published one, and which is genuinely necessary there; it is reassuring that the gadget actually satisfies it.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Section 4.2 (p. 7): 'let P = 1/2 and n := 3*401+1 = 1,204 ... By Lemma 4.1, the 1/2-percolation on Gn satisfies conditions of Lemma 3.3'.

import Definitions.Def_BunkbedPercolation
open Bunkbed Finset

namespace BunkbedFalse

/-- **The gadget at `P = 1/2` and `n = 1204` satisfies Eq. [1].** The three partition-probability
conditions required by the robustness lemma -- symmetry, strict positivity of the determinant, and
Eq. [1] with the constant 400 -- all hold for `G_1204` under `1/2`-percolation. -/
theorem gadget_eq1_at_half :
    Pab_c (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
        = Pac_b (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
    ∧ 0 < Pabc (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
          * Pa_b_c (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
        - Pab_c (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
          * Pac_b (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
    ∧ 400 * Pa_bc (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
        ≤ Pabc (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
          * Pa_b_c (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
        - Pab_c (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
          * Pac_b (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204) := by
  sorry

end BunkbedFalse
