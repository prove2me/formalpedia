-- Prove2me | Theorems.Thm_AnonymousDirectedCounting_Exact_core_counting_time
-- name    : AnonymousDirectedCounting.Exact.core_counting_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:32.340956+00:00
-- url     : https://prove2.me/theorems/87e4ca6b-e69d-4ca0-bea3-4b5651771a36
-- title:
--   Theorem 1 — core algorithm correctness and cost
-- statement:
--   For every admissible network with $n$ agents and $\ell$ leaders (so $1\le\ell\le n$), the core algorithm makes every agent output $n$ and halt at round $2n-1$, and no agent outputs earlier. Its local computations take time polynomial in $n$ whenever the network has at most $2^{\mathrm{poly}(n)}$ arcs per round, in the sense of the polynomial binary implementation clause. Correctness and timing need no arc bound.
--
--   The theorem concerns the execution with silent halting, so it includes the claim that all smaller candidates are rejected at every agent.
--
--   Differences from the source:
--   - encoding: anonymous agents and abstract history-tree nodes with fibers → external Fin n indexing, and nodes as values of History r with fibers computed from the network; reason: the index is absent from protocol inputs; two agents have equal History r exactly when they lie in one class of P_r, so nodes and vistas up to isomorphism are the same data
--   - encoding: levels -1, 0, 1, ... with the root at level -1 and b(root) set in Step 4 → levels 0, 1, ... only; reason: the root is the unique ancestor of everything; no check and no lemma reads it
--   - encoding: local computations take time polynomial in n assuming at most 2^{poly(n)} arcs per round, with each distinct received state given once with a binary multiplicity → HasPolynomialBinaryImplementation: one one-tape binary machine and one injective state encoding; for every p : Polynomial ℕ, constants C, k chosen before the network with at most C(1+n)^k steps in each executed round under the 2^{p(n)} arc promise; reason: the source fixes no machine model and no exponent; one-tape machines are polynomially equivalent to the usual models, and the constants depend only on p and the machine
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), Theorem 1, printed p. 8 (PDF p. 10)

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_Protocols
import Definitions.Def_AnonymousDirectedCounting_Exact_LocalCost

set_option autoImplicit false

namespace AnonymousDirectedCounting.Exact

/-- Theorem 1, printed p. 8 (PDF p. 10). For every `1 ≤ ℓ ≤ n` (both from admissibility), the core
algorithm makes all agents output `n` and halt at round `2n - 1`, and its local computations take
time polynomial in `n` under the arc promise. -/
theorem core_counting_time :
    (∀ (n : ℕ) (G : NetworkModel n), Admissible G →
      SimultaneousCountingAt coreProtocol G (2 * n - 1)) ∧
    HasPolynomialBinaryImplementation coreProtocol := by sorry

end AnonymousDirectedCounting.Exact
