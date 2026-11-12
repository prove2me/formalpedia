-- Prove2me | Theorems.Thm_BunkbedFalse_gadget_conn
-- name    : BunkbedFalse.gadget_conn
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-11T16:21:29.100346+00:00
-- url     : https://prove2.me/theorems/ee6619c8-e8e7-4156-911b-94ffdd5bb1c8
-- title:
--   Lemma 5.1 — $\mathbb{P}_P(a \leftrightarrow v_n)$ in the gadget $G_n$
-- statement:
--   Consider the gadget graph $G_n$ of Fig. 2: vertices $a$ and $v_1, \dots, v_n$, where each **spoke** $a$–$v_i$ is retained with probability $1-P$ and each **path** edge $v_i$–$v_{i+1}$ is retained with probability $P$. For $n \ge 3$ and $0 < P < 1$,
--
--   $$\mathbb{P}_P\bigl(a \leftrightarrow v_n\bigr) \;=\; \frac{1 - P^{2n}}{1 + P}.$$
--
--   The proof is a two-case recurrence on whether the spoke $(a, v_n)$ is open, giving $P_n = (1-P) + P^2 P_{n-1}$ with $P_0 = 0$, solved by induction.
--
--   This is the first of three elementary computations that together determine how well the gadget $G_n$ simulates a single hyperedge, which is the quantitative heart of the refutation.
--
--   **Formalization Note** Vertices are `Fin (n+1)` with $a = 0$ and $v_i = i$, so $v_n$ is `Fin.last n`. The weight function assigns $1-P$ to any edge meeting $0$ and $P$ to the rest.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, "The bunkbed conjecture is false", Proc. Natl. Acad. Sci. USA 122 (2025), no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122 - p. 8, Lemma 5.1.

import Definitions.Def_BunkbedHypergraph
open Bunkbed Bunkbed.Hyper SimpleGraph Finset

namespace BunkbedFalse

/-- **Lemma 5.1** (Gladkov–Pak–Zimin, PNAS 122 (2025) e2420725122, p. 8). For the gadget
graph `Gₙ` of Fig. 2, `ℙ_P(a ↔ vₙ) = (1 - P^{2n})/(1 + P)`. -/
theorem gadget_conn (n : ℕ) (P : ℚ) (hn : 3 ≤ n) (hP0 : 0 < P) (hP1 : P < 1) :
    connProb (gadgetE n) (gadgetW n P) 0 (Fin.last n) = (1 - P ^ (2 * n)) / (1 + P) := by sorry

end BunkbedFalse
