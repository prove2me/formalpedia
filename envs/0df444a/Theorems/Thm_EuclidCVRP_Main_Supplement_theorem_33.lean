-- Prove2me | Theorems.Thm_EuclidCVRP_Main_Supplement_theorem_33
-- name    : EuclidCVRP.Main.Supplement.theorem_33
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:15:04.449365+00:00
-- url     : https://prove2.me/theorems/a754ecd4-8efa-409c-b486-ae85a4838fff
-- title:
--   Theorem 33 (companion theorem; not used in the proof of the goal) — PTAS for polynomially bounded capacity
-- statement:
--   Let $c\in\mathbb N$ be a fixed bound parameter and let $\varepsilon>0$ be any real accuracy. Consider Euclidean unsplittable capacitated vehicle routing with a depot and $n\ge0$ clients, capacity $Q\ge1$, and integer demands $0\le d(v)\le Q$. Restrict the instances to
--
--   $$Q\le c(n+1)^c.$$
--
--   There exists one polynomial-time algorithm, depending on $c$ and $\varepsilon$, that returns a feasible collection $\mathcal T$ of depot tours on every valid instance in this class. Every client is served exactly once, each tour has total demand at most $Q$, and, writing $\operatorname{cost}$ for total Euclidean length,
--
--   $$\operatorname{cost}(\mathcal T)\le(1+\varepsilon)\operatorname{cost}(\mathcal T')\qquad\text{for every feasible collection }\mathcal T'.$$
--
--   This is a polynomial-time approximation scheme for every fixed polynomial capacity bound: every polynomial in $n$ with natural coefficients is bounded above by $c(n+1)^c$ for some $c$. Runtime is polynomial in the complete encoded input bit length for each fixed $c,\varepsilon$; neither parameter depends on the input instance. There is no bound on the number of tours or the distances to the depot, and clients of zero demand, coincident clients and clients at the depot are included.
--
--   **Formalization Note** The published base mission model is used unchanged, including rational coordinates, binary integers, exact Euclidean distance and the finite-alphabet TM2 computation model. The coefficient $1$ in $1+\varepsilon$ is exact; there is no hidden approximation constant. The parameter $c$ describes the input class, not an absolute approximation constant. At $c=0$ the class contains no valid positive-capacity instances; every $c\ge1$ includes valid instances, and no assumption $c>0$ is needed.
--
--   Differences from the source:
--   - reading: capacity Q ≤ n^{O(1)} → for every fixed natural c, capacity Q ≤ c·(n+1)^c, with the algorithm chosen after c and ε; reason: these bounds cover every fixed polynomial bound in n, and the shift preserves meaningful bounds at n = 0 and n = 1
--   - reading: polynomial-time algorithm with no machine model specified → the published IsApproxAlg model: rational-coordinate binary inputs, binary capacity and demands, and Mathlib TM2ComputableInPolyTime with finite stack alphabets, polynomial in the complete input bit length; reason: inherits the immutable base mission computational convention; the same machine works for all valid inputs in the fixed capacity class and halts in polynomial time on every raw bit string
--   - encoding: collections of depot tours serving each client exactly once → the published list of tours, each a list of zero-based client indices, allowing empty tours of cost zero; reason: inherits the base model unchanged; empty tours affect neither feasibility nor cost, coincident locations remain separately indexed clients, and each tour respects capacity Q exactly
--   - encoding: cost at most (1+ε) times the optimum → cost at most (1+ε) times the cost of every feasible solution; reason: a valid finite instance has a feasible solution and an attained minimum; this is the published approximation predicate and does not substitute a relaxation
-- source:
--   Jannis Blauth, Fabrizio Grandoni, Bence Mátravölgyi, Ramin Mousavi, Kinter Ren, Mohammad R. Salavatipour, STOC 2027 submission #1236 (October 2026), §5, Theorem 33, p. 31

import Mathlib
import Definitions.Def_EuclidCVRP_Main_Machine

set_option autoImplicit false

namespace EuclidCVRP.Main.Supplement

/-- Theorem 33, Section 5, p. 31 of Blauth, Grandoni, Mátravölgyi, Mousavi, Ren and
Salavatipour, STOC 2027 submission #1236 (October 2026).

For every fixed polynomial capacity bound and every real accuracy ε > 0, there is a
polynomial-time (1 + ε)-approximation on every valid instance satisfying that bound.
The bounds c * (n + 1)^c, for natural c, cover every fixed polynomial bound in n.
The machine is chosen after c and ε and is uniform over instances. The published
IsApproxAlg supplies exact capacity feasibility, Euclidean cost, rational-coordinate
binary inputs and finite-alphabet TM2 polynomial time in the complete input bit length.
No bounded-distance or number-of-tours hypothesis is imposed. -/
theorem theorem_33 (c : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ alg : List Bool → List (List ℕ),
      EuclidCVRP.Main.IsApproxAlg (1 + ε)
        (fun J => J.Q ≤ c * (J.n + 1) ^ c) alg := by sorry

end EuclidCVRP.Main.Supplement
