-- Prove2me | Theorems.Thm_BunkbedFalse_gadget_partition_bound
-- name    : BunkbedFalse.gadget_partition_bound
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-11T16:56:49.856009+00:00
-- url     : https://prove2.me/theorems/ef00496c-c295-48bb-8423-f4831050e95c
-- title:
--   Proposition 5.4 — partition-probability bound for $G_n$
-- statement:
--   Combining the three preceding computations for the gadget graph $G_n$ ($n \ge 3$, $0 < P < 1$): first,
--
--   $$P_{a|bc} \;=\; P^{2n-1},$$
--
--   and second, the quantity controlling how faithfully $G_n$ simulates a hyperedge satisfies
--
--   $$P_{abc}\,P_{a|b|c} \;-\; P_{ac|b}\,P_{ab|c} \;\ge\; \Bigl(n\,\frac{1-P}{1+P} \;-\; 1\Bigr) P^{2n-1}.$$
--
--   Here the five quantities are the probabilities that the percolation partitions the triple $a = 0$, $b = v_1$, $c = v_n$ in each of the five possible ways. The point of the bound is that the left-hand side can be made arbitrarily large relative to $P_{a|bc}$ by taking $n$ large, which is exactly what the robust hyperedge lemma requires.
--
--   **Formalization Note** The inequality is stated with $\ge$, as in the source; Lemma 4.1 then derives the strict form.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, "The bunkbed conjecture is false", Proc. Natl. Acad. Sci. USA 122 (2025), no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122 - p. 8, Proposition 5.4.

import Definitions.Def_BunkbedHypergraph
open Bunkbed Bunkbed.Hyper SimpleGraph Finset

namespace BunkbedFalse

/-- **Proposition 5.4** (p. 8). -/
theorem gadget_partition_bound (n : ℕ) (P : ℚ) (hn : 3 ≤ n) (hP0 : 0 < P) (hP1 : P < 1) :
    Pa_bc (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) = P ^ (2 * n - 1) ∧
    Pabc (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) * Pa_b_c (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) - Pac_b (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) * Pab_c (gadgetE n) (gadgetW n P) 0 1 (Fin.last n)
      ≥ (n * (1 - P) / (1 + P) - 1) * P ^ (2 * n - 1) := by sorry

end BunkbedFalse
