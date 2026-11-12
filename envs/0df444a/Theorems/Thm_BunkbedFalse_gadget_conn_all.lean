-- Prove2me | Theorems.Thm_BunkbedFalse_gadget_conn_all
-- name    : BunkbedFalse.gadget_conn_all
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-11T16:25:51.454528+00:00
-- url     : https://prove2.me/theorems/d32add11-058b-484c-a7c0-3b5910d8184c
-- title:
--   Lemma 5.2 — $\mathbb{P}_P(a \leftrightarrow v_1 \leftrightarrow v_n)$
-- statement:
--   In the gadget graph $G_n$ (spokes $a$–$v_i$ open with probability $1-P$, path edges $v_i$–$v_{i+1}$ open with probability $P$), for $n \ge 3$ and $0 < P < 1$,
--
--   $$\mathbb{P}_P\bigl(a \leftrightarrow v_1 \leftrightarrow v_n\bigr) \;=\; \frac{1 - P^{2n}}{(1+P)^2} \;+\; \frac{n(1-P)P^{2n-1}}{1+P}.$$
--
--   That is: the probability that $a$, $v_1$ and $v_n$ all lie in one component. The proof splits on which of the two spokes $(a,v_1)$ and $(a,v_n)$ are open, yielding the recurrence $P_n = (1-P)^2 + 2P^2 P_{n-1} - P^4 P_{n-2}$ with $P_0 = 0$ and $P_1 = 1-P$.
--
--   **Formalization Note** This is the partition probability $P_{abc}$ for the triple $a = 0$, $b = v_1$, $c = v_n$, i.e. the probability that the percolation places all three in a single component.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, "The bunkbed conjecture is false", Proc. Natl. Acad. Sci. USA 122 (2025), no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122 - p. 8, Lemma 5.2.

import Definitions.Def_BunkbedHypergraph
open Bunkbed Bunkbed.Hyper SimpleGraph Finset

namespace BunkbedFalse

/-- **Lemma 5.2** (p. 8). `ℙ_P(a ↔ v₁ ↔ vₙ) = (1-P^{2n})/(1+P)² + n(1-P)P^{2n-1}/(1+P)`. -/
theorem gadget_conn_all (n : ℕ) (P : ℚ) (hn : 3 ≤ n) (hP0 : 0 < P) (hP1 : P < 1) :
    Pabc (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) = (1 - P ^ (2 * n)) / (1 + P) ^ 2 + n * (1 - P) * P ^ (2 * n - 1) / (1 + P) := by
  sorry

end BunkbedFalse
