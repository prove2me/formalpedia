-- Prove2me | Theorems.Thm_BNCovPack_Routing_lemma_5_4
-- name    : BNCovPack.Routing.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:37:51.712946+00:00
-- url     : https://prove2.me/theorems/acd12f35-d0e5-46cb-8271-5976e1ef8b1a
-- title:
--   Lemma 5.4 — the online routing algorithm respects capacities and serves ≥ OPT/(4B ln 2 · ln(P(max)+2)) − 1 requests
-- statement:
--   Let $E$ be a non-empty finite set of $m$ edges with capacities $u(e) > 0$, let $\sigma$ be a sequence of requests whose paths have at most $P(\max)$ edges each, and let $B = \exp(1 + \ln(2m)/u(\min)) - 1$. Run the integral online routing algorithm of Section 5.2 on $\sigma$, and let $\chi(e)$ be the number of chosen paths through edge $e$ and $\sum_{r_i} \chi(r_i)$ the number of served requests. Then
--
--   1. no capacity is violated: $\chi(e) \le u(e)$ for every edge $e$;
--   2. for every feasible fractional routing $f$ of $\sigma$ (in particular an optimal one, of value $\mathrm{OPT}$),
--
--   $$
--   \sum_{r_i} \chi(r_i) \ \ge\ \frac{\mathrm{val}(f)}{4B \ln 2 \cdot \ln\big(P(\max)+2\big)} - 1 .
--   $$
--
--   Since every integral routing is a feasible fractional routing, the bound holds against the integral optimum as well. This is the paper's deterministic online algorithm for throughput-competitive routing of virtual circuits, matching the competitive factor of Awerbuch, Azar and Plotkin.
--
--   **Formalization Note** The paper writes $O(\log P(\max) \cdot [\exp(1 + 2\ln m/u(\min)) - 1])$; the proof yields the explicit bound above, with the rounding scale $B = \exp(1+\ln(2m)/u(\min)) - 1$ chosen on p. 15 and the fractional factor $2\ln(1+\ell) = 2\ln(P(\max)+2)$. For $m \ge 2$, $\ln(2m) \le 2\ln m$, so this is at least as strong as the printed rate; at $m = 1$ the printed "$2 \ln m$" $= 0$ does not follow from the proof, and the proof's constant is stated. Paths are arbitrary finite edge sets (simple paths of a graph are a special case), and $P(\max)$ is any upper bound on their size.
-- source:
--   Buchbinder, Naor, Online Primal-Dual Algorithms for Covering and Packing, Math. Oper. Res. (2009), DOI 10.1287/moor.1080.0363, p. 16, Lemma 5.4 (proof pp. 16–17)

import Mathlib
import Definitions.Def_BNCovPack_Routing_Routing
import Definitions.Def_BNCovPack_Routing_Potential
import Definitions.Def_BNCovPack_Routing_Algorithm

namespace BNCovPack.Routing

/-- Lemma 5.4, Buchbinder–Naor 2009, p. 16 (explicit form from the proof, pp. 16–17). Let `E` be
a non-empty finite set of `m` edges with capacities `u e > 0`, let every path of every request in
`σ` have at most `Pmax` edges, and let `B = exp(1 + ln(2m)/u(min)) − 1`. After the online routing
algorithm of §5.2 has processed `σ`:
1. no capacity is violated: `χ(e) ≤ u(e)` for every edge `e`;
2. the number of served requests is at least `OPT/(4 B ln 2 · ln(Pmax + 2)) − 1`, where `OPT` is the
   value of any feasible fractional routing of `σ`. -/
theorem lemma_5_4 {E : Type*} [Fintype E] [Nonempty E] [DecidableEq E] (u : E → ℝ)
    (hu : ∀ e, 0 < u e) (Pmax : ℕ) (σ : List (List (Finset E)))
    (hP : ∀ ps ∈ σ, ∀ P ∈ ps, P.card ≤ Pmax) :
    (∀ e, ((algorithm u Pmax σ).chi e : ℝ) ≤ u e) ∧
    ∀ f : List (List ℝ), IsFeasibleRouting u σ f →
      routingValue f / (4 * roundingScale u * Real.log 2 * Real.log ((Pmax : ℝ) + 2)) - 1 ≤
        ((algorithm u Pmax σ).served : ℝ) := by sorry

end BNCovPack.Routing
