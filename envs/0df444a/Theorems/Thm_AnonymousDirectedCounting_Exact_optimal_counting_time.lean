-- Prove2me | Theorems.Thm_AnonymousDirectedCounting_Exact_optimal_counting_time
-- name    : AnonymousDirectedCounting.Exact.optimal_counting_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:32.185298+00:00
-- url     : https://prove2.me/theorems/1351c38e-6b3e-4341-9074-560d24f7a310
-- title:
--   Theorem 2 — exact worst-case Counting time with polynomial local computation
-- statement:
--   For $n\ge1$ and $1\le\ell\le n$ let
--   $$
--   T(n,\ell)=\begin{cases}n&n=\ell,\\2n-1&n>\ell,\ \ell=1,\\2n-2&n>\ell,\ \ell\ge2.\end{cases}
--   $$
--   The exact worst-case termination time for Counting over directed multigraphs is $T(n,\ell)$, in three parts. First, on every admissible network with $n$ agents and $\ell$ leaders, the combined algorithm makes every agent output $n$ and halt at round $T(n,\ell)$ and not before. Second, for every deterministic protocol that solves Counting on all sizes and leader sets, with arbitrary state and local computation, and every $1\le\ell\le n$, there is an admissible network with $n$ agents and $\ell$ leaders on which not all agents have halted before round $T(n,\ell)$. Third, the local computations of the combined algorithm take time polynomial in $n$ on networks with at most $2^{\mathrm{poly}(n)}$ arcs per round.
--
--   The optimum equality follows from the first two parts. The arc promise concerns only the third.
--
--   Differences from the source:
--   - encoding: anonymous agents and abstract history-tree nodes with fibers → external Fin n indexing, and nodes as values of History r with fibers computed from the network; reason: the index is absent from protocol inputs; two agents have equal History r exactly when they lie in one class of P_r, so nodes and vistas up to isomorphism are the same data
--   - encoding: levels -1, 0, 1, ... with the root at level -1 and b(root) set in Step 4 → levels 0, 1, ... only; reason: the root is the unique ancestor of everything; no check and no lemma reads it
--   - encoding: local computations take time polynomial in n assuming at most 2^{poly(n)} arcs per round, with each distinct received state given once with a binary multiplicity → HasPolynomialBinaryImplementation: one one-tape binary machine and one injective state encoding; for every p : Polynomial ℕ, constants C, k chosen before the network with at most C(1+n)^k steps in each executed round under the 2^{p(n)} arc promise; reason: the source fixes no machine model and no exponent; one-tape machines are polynomially equivalent to the usual models, and the constants depend only on p and the machine
--   - generalization: the exact worst-case termination time is T(n, ℓ) → the combined algorithm halts all agents at exactly T(n, ℓ) on every admissible network, together with a matching lower bound for every protocol; reason: Appendix C, printed p. 20, says all agents halt together at the round stated; a worst case of T(n, ℓ) follows, as does the optimum equality
--   - encoding: termination is the first round by which every agent has halted; no earlier than T → AllHalted at t implies T(n, ℓ) ≤ t; reason: halted cells stay halted, so this is the same statement and needs no infimum
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), Theorem 2, printed p. 11 (PDF p. 13); Section 3.2 and Appendices C–D, printed pp. 9–10, 19–23 (PDF pp. 11–12, 21–25)

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_Protocols
import Definitions.Def_AnonymousDirectedCounting_Exact_LocalCost

set_option autoImplicit false

universe u

namespace AnonymousDirectedCounting.Exact

/-- Theorem 2, printed p. 11 (PDF p. 13). The exact worst-case termination time is `T(n, ℓ)`:
the combined algorithm makes all agents output `n` and halt exactly at `T(n, ℓ)` on every admissible
network; for every protocol solving Counting and every `1 ≤ ℓ ≤ n`, some admissible `n`-agent network
with `ℓ` leaders does not terminate before `T(n, ℓ)`; and the local computations of the combined
algorithm take time polynomial in `n` under the arc promise. -/
theorem optimal_counting_time :
    (∀ (n : ℕ) (G : NetworkModel n), Admissible G →
      SimultaneousCountingAt sharpProtocol G (sharpTime n G.leaders.card)) ∧
    (∀ (S : Type u) (A : Protocol S), SolvesCounting A →
      ∀ n ell : ℕ, 1 ≤ ell → ell ≤ n →
        ∃ G : NetworkModel n, Admissible G ∧ G.leaders.card = ell ∧
          ∀ t : ℕ, AllHalted A G t → sharpTime n ell ≤ t) ∧
    HasPolynomialBinaryImplementation sharpProtocol := by sorry

end AnonymousDirectedCounting.Exact
