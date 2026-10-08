-- Prove2me | Theorems.Thm_BNCovPack_Routing_theorem_3_2
-- name    : BNCovPack.Routing.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:17:15.875065+00:00
-- url     : https://prove2.me/theorems/25f18e6a-971b-4800-9512-991f1b9c99f9
-- title:
--   Theorem 3.2 (packing half, with the oracle) — the fractional routing scheme is feasible and 2 ln(P(max)+2)-competitive
-- statement:
--   Let $E$ be a finite set of edges with capacities $u(e) > 0$, and let $\sigma$ be a sequence of requests, each given by a finite list of paths (sets of edges) with at most $P(\max)$ edges each. Run the $\{0,1\}$ online fractional packing scheme with the oracle, with $\ell = P(\max)+1$ and $B' = 2\ln(1+\ell) = 2\ln(P(\max)+2)$, and let $f^{\mathrm{alg}}$ be the flows it produces. Then
--
--   1. $f^{\mathrm{alg}}$ is a feasible fractional routing of $\sigma$ (non-negative, at most $1$ per request, at most $u(e)$ through each edge);
--   2. for every feasible fractional routing $f$ of $\sigma$,
--
--   $$
--   \mathrm{val}(f) \le 2\ln\big(P(\max)+2\big) \cdot \mathrm{val}(f^{\mathrm{alg}}).
--   $$
--
--   This is the first phase of the two-phase approach of Section 5.2: a feasible fractional routing within a logarithmic factor of the fractional optimum, produced online.
--
--   **Formalization Note** The paper writes $O(\log \ell)$ and states Theorem 3.2 for general $\{0,1\}$ packing; its proof "follows along the same lines as the proof of Theorem 3.1" with $n$ replaced by $\ell$, which with $B' = 2\ln(1+\ell)$ yields feasibility (claim (iii)) and the factor $B' = 2\ln(1+\ell)$ (claim (i) and weak duality). Only the packing half, on the routing instance, is stated; the covering half is not used by the mission.
-- source:
--   Buchbinder, Naor, Online Primal-Dual Algorithms for Covering and Packing, Math. Oper. Res. (2009), DOI 10.1287/moor.1080.0363, p. 5, Theorem 3.2 and the oracle remark; applied as in Section 5.2, p. 15

import Mathlib
import Definitions.Def_BNCovPack_Routing_Routing
import Definitions.Def_BNCovPack_Routing_FracScheme

namespace BNCovPack.Routing

/-- Theorem 3.2 (packing half, with the oracle remark), Buchbinder–Naor 2009, p. 5, on the
routing problem of §5.2 (Fig. 3, p. 14). Let `E` be a finite set of edges with capacities
`u e > 0`, let every path of every request have at most `Pmax` edges, and run the `{0,1}`
fractional scheme with `ℓ = Pmax + 1` and `B' = 2 ln(1 + ℓ) = 2 ln(Pmax + 2)` on the request
sequence `σ`. Then the flows it produces form a feasible fractional routing of `σ`, and every
feasible fractional routing `f` of `σ` has value at most `2 ln(Pmax + 2)` times the scheme's. -/
theorem theorem_3_2 {E : Type*} [Fintype E] [DecidableEq E] (u : E → ℝ) (hu : ∀ e, 0 < u e)
    (Pmax : ℕ) (σ : List (List (Finset E))) (hP : ∀ ps ∈ σ, ∀ P ∈ ps, P.card ≤ Pmax) :
    IsFeasibleRouting u σ (fracRun u (Pmax + 1) (2 * Real.log ((Pmax : ℝ) + 2)) σ).flows ∧
    ∀ f : List (List ℝ), IsFeasibleRouting u σ f →
      routingValue f ≤ 2 * Real.log ((Pmax : ℝ) + 2) *
        routingValue (fracRun u (Pmax + 1) (2 * Real.log ((Pmax : ℝ) + 2)) σ).flows := by sorry

end BNCovPack.Routing
