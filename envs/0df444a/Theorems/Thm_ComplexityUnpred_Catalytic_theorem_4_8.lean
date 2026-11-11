-- Prove2me | Theorems.Thm_ComplexityUnpred_Catalytic_theorem_4_8
-- name    : ComplexityUnpred.Catalytic.theorem_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:03:48.158212+00:00
-- url     : https://prove2.me/theorems/94a3611a-d63a-4e13-b7b7-7f4388b970e4
-- title:
--   Theorem 4.8 — WeakExcess reduces to UNPRED in polynomial time
-- statement:
--   **WeakExcess** asks, given $n,\ell$ in unary, a circuit $C$ on $n+\ell$ inputs and the table of $\mathrm{ind}:\{0,1\}^\ell\to[n]$, describing a hidden deterministic hypercube digraph $G$ with $\mathrm{EdgeExists}(v,l)=C(v,l)$, for a vertex $v$ with $\text{out-degree}_G(v)\ge\text{in-degree}_G(v)$. **UNPRED** asks, given $n$, $\epsilon=1/r$ and middle-bit predictor circuits $P_1,\dots,P_m$ with indices, for a non-empty multiset $S\subseteq\{0,1\}^n$ with $\mathrm{adv}_{U(S)}(\{P_1,\dots,P_m\})<\epsilon$. The theorem states
--   $$\textsf{WeakExcess}\le_P\textsf{UNPRED}:$$
--   there are deterministic polynomial-time maps $f$ (instances) and $g$ (solutions) such that for every valid WeakExcess instance $x$, $f(x)$ is a valid UNPRED instance and $g(x,S)$ is a WeakExcess solution of $x$ for **every** UNPRED solution $S$ of $f(x)$, however large.
--
--   It is the last link of the chain FastCatTape $\to$ LossyCoding $\to$ WeakExcess $\to$ UNPRED.
--
--   **Formalization Note** $\le_P$ is the published `CardinalMatching.SearchReduces`; both problems are search problems on bit strings with the codes of their definitions.
--
--   Differences from the source:
--   - encoding: ≤P: both maps computable in deterministic polynomial time → CardinalMatching.SearchReduces with CookPvsNP.PolyTimeComputable (one-tape Cook machines, time |x|^k + k); the solution map reads the tagged pair (x, y); reason: the published platform reduction; it requires correctness for every answer, as §2.2 does
--   - encoding: WeakExcess instance: n, ℓ in unary, circuit C, ind as an explicit table → WeakExcessInstance.encode (unary n, ℓ; circuit code; 2^ℓ table entries in lexicographic label order, 1-based, binary); reason: one concrete binary code of the paper's input
--   - encoding: answer: out-degree ≥ in-degree in the hidden deterministic hypercube digraph G with EdgeExists = C → out-degree ≥ in-degree in HypercubeDigraph.ofOracle ind C; reason: every such G has the same non-self-loop edges as ofOracle ind C, and self-loops do not change out − in, so the answer set is the same
--   - encoding: UNPRED instances (n, r in unary, circuits, indices) and multiset answers, no code fixed → the codes UnpredInstance.encode and encStrings of the UNPRED definition; reason: one concrete prefix-free binary code, polynomially equivalent to any reasonable one
--   - reading: THRESHOLD gates with unspecified thresholds → gates Th_t (at least t inputs are 1), t in the gate label; reason: the paper does not fix the thresholds; Th_t is the standard reading and keeps the gate in the basis
-- source:
--   Agarwala, Dorfman, The Complexity of Unpredictability, arXiv:2611.05956v1, p. 32, Theorem 4.8

import Mathlib
import Definitions.Def_CardinalMatching_SearchReduces
import Definitions.Def_ComplexityUnpred_Catalytic_UNPRED
import Definitions.Def_ComplexityUnpred_Catalytic_WeakExcess

namespace ComplexityUnpred.Catalytic

/-- **Theorem 4.8** (Agarwala, Dorfman, arXiv:2611.05956v1, p. 32): `WeakExcess ≤_P UNPRED`. -/
theorem theorem_4_8 : CardinalMatching.SearchReduces WeakExcess UNPRED := by sorry

end ComplexityUnpred.Catalytic
