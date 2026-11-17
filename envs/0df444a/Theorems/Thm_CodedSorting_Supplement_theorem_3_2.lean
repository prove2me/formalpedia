-- Prove2me | Theorems.Thm_CodedSorting_Supplement_theorem_3_2
-- name    : CodedSorting.Supplement.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:50:35.028205+00:00
-- url     : https://prove2.me/theorems/9940704a-cb02-4a2b-87fe-74239c063b8a
-- title:
--   Theorem 3.2 — a strict coding advantage in undirected multiple-unicast networks, $R_{\mathrm{route}} \le 1 - 33/338432 < 1 = R_{\mathrm{code}}$
-- statement:
--   In an undirected multiple-unicast network every edge has a capacity shared by its two directions, and there are $W$ sessions; session $i$ sends an independent message from its source $s_i$ to its sink $t_i\ne s_i$. $R_{\mathrm{route}}$ is the maximum common rate achievable by fractional routing, and $R_{\mathrm{code}}$ is the supremum of the common rates $k/T$ of finite-round binary linear protocols (every transmitted bit is an XOR of bits available at the sender, schedule fixed in advance, one bit per edge per round in one direction, zero-error decoding at every sink).
--
--   **Theorem.** There is a finite undirected multiple-unicast network with no loops or parallel edges, unit edge capacities, and independent source messages such that
--   $$
--   R_{\mathrm{route}} \;\le\; 1-\frac{33}{338432} \;<\; 1 \;=\; R_{\mathrm{code}}.
--   $$
--   Concretely, there are a finite simple graph $G$ and sessions $s_i\to t_i$ with $s_i\ne t_i$ such that:
--
--   1. every common rate $\lambda\ge0$ of a fractional routing in the unit-capacity network satisfies $\lambda\le 1-33/338432$;
--   2. $1-33/338432<1$;
--   3. $1$ is the least upper bound of the common rates of correct binary linear protocols on the same network.
--
--   Network coding thus strictly beats fractional routing on this undirected network, which refutes the multiple-unicast conjecture for its rate vector.
--
--   **Formalization Note** The graph is a `SimpleGraph` on `Fin n`. The routing bound is stated for every feasible $\lambda$ of the unit-capacity network (`unitNetwork`, built on the published `GeometryOfGraphs.FlowCut.Network`), which is the bound on the maximum. $R_{\mathrm{code}}=1$ is `IsLUB (codeRates G s t) 1`: rate $1$ itself need not be attained.
--
--   Differences from the source:
--
--   - encoding: fractional routing assigns flow to source–sink paths → arc-form feasible concurrent flow with demand 1 per session (the published IsFeasibleFlow); reason: flow decomposition gives the same set of feasible common rates
--   - encoding: R_route ≤ 1 − 33/338432 for the maximum common routing rate → every feasible common rate λ ≥ 0 satisfies λ ≤ 1 − 33/338432; reason: equivalent, and avoids Lean's sSup convention on unbounded sets
--   - encoding: R_code = 1, the supremum of common rates → IsLUB (codeRates G s t) 1; reason: same supremum; Lean's sSup is 0 on empty or unbounded sets
--   - encoding: independent source messages → zero-error decoding for every input in (𝔽₂^k)^W; reason: the paper's zero-error requirement over every source input; no joint law is involved
-- source:
--   B. Li, Z. Li, S. Liu, Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), Theorem 3.2, p.5 (PDF 6), display (3); model §3.2, p.5; proof §5.3, pp.17–18 (PDF 18–19)

import Mathlib
import Definitions.Def_GeometryOfGraphs_FlowCut_Network
import Definitions.Def_GeometryOfGraphs_FlowCut_Maxflow
import Definitions.Def_CodedSorting_Supplement_unitNetwork
import Definitions.Def_CodedSorting_Supplement_LinearProtocol

namespace CodedSorting

namespace Supplement

open GeometryOfGraphs.FlowCut

/-- **Theorem 3.2** (A strict coding advantage in undirected multiple-unicast networks;
B. Li, Z. Li, S. Liu, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), p.5 (PDF 6)).
There is a finite undirected multiple-unicast network with no loops or parallel edges, unit edge
capacities, and independent source messages such that
`R_route ≤ 1 − 33/338432 < 1 = R_code`.

**Formalization Note** The network is a `SimpleGraph` on `Fin n` (finite, no loops, no parallel
edges) with `W` sessions `s i → t i`, `s i ≠ t i`, and unit capacities (`unitNetwork`).
`R_route ≤ 1 − 33/338432` is stated for every feasible common routing rate `λ ≥ 0` (the paper's
(11)), which is the bound on the maximum. `R_code = 1` is `IsLUB (codeRates G s t) 1`: `1` is the
least upper bound of the rates `k/T` of correct finite-round binary linear protocols; it need not
be attained. Independence of the messages is encoded by zero-error correctness on every input in
`(𝔽₂^k)^W`. -/
theorem theorem_3_2 :
    ∃ (n W : ℕ) (G : SimpleGraph (Fin n)) (s t : Fin W → Fin n),
      (∀ i, s i ≠ t i) ∧
      (∀ (lam : ℝ) (f : Fin W → Fin n → Fin n → ℝ), 0 ≤ lam →
        (unitNetwork G s t).IsFeasibleFlow f lam → lam ≤ 1 - 33 / 338432) ∧
      (1 - 33 / 338432 : ℝ) < 1 ∧
      IsLUB (codeRates G s t) 1 := by sorry

end Supplement

end CodedSorting
