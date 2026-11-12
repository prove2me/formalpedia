-- Prove2me | Theorems.Thm_BunkbedFalse_hyperedge_simulation
-- name    : BunkbedFalse.hyperedge_simulation
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-11T16:57:49.338459+00:00
-- url     : https://prove2.me/theorems/0f0fab8b-f3a0-4e9f-bf4b-74ff51f92b37
-- title:
--   Lemma 4.1 — hyperedge simulation by the gadget $G_n$
-- statement:
--   Let $n \ge 3$ and $0 < P < 1$, and consider the weighted gadget graph $G_n$ on $n+1$ vertices, with $b = v_1$ and $c = v_n$. Then the two "mixed" partition probabilities agree,
--
--   $$P_{ab|c} \;=\; P_{ac|b},$$
--
--   and
--
--   $$P_{abc}\,P_{a|b|c} \;-\; P_{ab|c}\,P_{ac|b} \;>\; \Bigl(n\,\frac{1-P}{1+P} - 1\Bigr) P_{a|bc}.$$
--
--   This is the **hyperedge simulation** lemma. A single $3$-hyperedge cannot be simulated exactly by bond percolation on any graph, so the strategy is instead to show that $G_n$ simulates one *well enough*: the displayed inequality says the simulation error can be driven below any prescribed threshold by increasing $n$. Taking $P = 1/2$ and $n = 3 \cdot 401 + 1 = 1204$ makes the right-hand side exceed the factor $400$ demanded by the robust hyperedge lemma, which is what produces the counterexample.
--
--   **Formalization Note** The five partition probabilities are those of the triple $a = 0$, $b = v_1$, $c = v_n$ in $G_n$. The symmetry $P_{ab|c} = P_{ac|b}$ reflects the reflection symmetry of $G_n$ exchanging $v_1$ and $v_n$.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, "The bunkbed conjecture is false", Proc. Natl. Acad. Sci. USA 122 (2025), no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122 - p. 7, Lemma 4.1 (Eq. [1]); proof p. 8.

import Definitions.Def_BunkbedHypergraph
open Bunkbed Bunkbed.Hyper SimpleGraph Finset

namespace BunkbedFalse

/-- **Lemma 4.1** (hyperedge simulation, p. 7). -/
theorem hyperedge_simulation (n : ℕ) (P : ℚ) (hn : 3 ≤ n) (hP0 : 0 < P) (hP1 : P < 1) :
    Pab_c (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) = Pac_b (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) ∧
    Pabc (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) * Pa_b_c (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) - Pab_c (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) * Pac_b (gadgetE n) (gadgetW n P) 0 1 (Fin.last n)
      > (n * (1 - P) / (1 + P) - 1) * Pa_bc (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) := by sorry

end BunkbedFalse
