-- Prove2me | Theorems.Thm_DetCCHard_theorem_5_2
-- name    : DetCCHard.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:37:32.448199+00:00
-- url     : https://prove2.me/theorems/94d4740e-20b3-4256-bd47-1ba601aa8ce2
-- title:
--   Theorem 5.2 — bounded-degree coloring source: 3-SAT reduces to gap 3-coloring of almost-linear size
-- statement:
--   There are constants $\Delta \ge 1$ and rational $\gamma > 0$ and a deterministic polynomial-time reduction from 3-SAT to nonempty loopless multigraphs $G = (V, E)$ with no isolated vertices and maximum degree at most $\Delta$ such that:
--
--   1. a satisfiable formula produces a 3-colorable graph;
--   2. an unsatisfiable formula produces a graph for which every 3-coloring has at least $\gamma|E|$ monochromatic edge occurrences.
--
--   Moreover, for every density bound $c_s$ there is a fixed positive integer $p$ such that for every formula on $N \ge 1$ variables with at most $c_s N$ clauses the output satisfies, with $n = |V|$,
--   $$
--   N \le |E|, \qquad n,\ |E| \le N(\log(N+2))^p, \qquad n/2 \le |E| \le \Delta n/2 .
--   $$
--
--   This is the PCP-strength source of the whole reduction: it is posed here, not assumed.
--
--   **Formalization Note** The reduction is a string function, polynomial-time in the sense of the published `CookPvsNP.PolyTimeComputable`, whose output is the explicit encoding of the graph. Logarithms are binary.
--
--   Differences from the source:
--   - generalization: 3-CNF formula (three literals per clause) → every clause has at most three literals; reason: formulas with exactly three literals per clause are a special case
--   - encoding: 3-CNF formulas as input strings (format unspecified) → the published CookPvsNP.encodeCNF, variable indices in unary; reason: renaming variables to 0, …, N−1 is polynomial-time, so unary and binary encodings are interconvertible in polynomial time
--   - reading: a formula on N variables → N = number of distinct variable indices occurring in the formula; reason: the only variable count a CNF determines without a declared universe
--   - reading: sparse formulas: at most c_s N clauses, c_s fixed in advance; a fixed positive integer p → for every real c_s there is p > 0 (p chosen after c_s); reason: §4.1, p.13: constants may depend on c_s
--   - encoding: the output graph → the string encodeGraph G (n and the edge occurrences in binary); reason: an explicit injective encoding; the paper fixes no format
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Theorem 5.2, pp.16–17 (proof in §G.1, pp.70–71)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_DetCCHard_SrcGraph
import Definitions.Def_DetCCHard_CodeSym
import Definitions.Def_DetCCHard_encodeGraph
import Definitions.Def_DetCCHard_Is3CNF

namespace DetCCHard

/-- **Theorem 5.2 (Bounded-degree coloring source)** (Gaspers–He–Mackenzie, arXiv:2508.05597,
held version sha256 ad552d13…a4a03, Theorem 5.2, pp.16–17). There are constants `Δ ≥ 1` and
rational `γ > 0` and a deterministic polynomial-time reduction from 3-SAT to nonempty loopless
multigraphs with no isolated vertices and maximum degree at most `Δ` such that a satisfiable
formula produces a 3-colorable graph and an unsatisfiable formula produces a graph every
3-coloring of which has at least `γ|E|` monochromatic edge occurrences. For sparse formulas (at
most `c_s N` clauses on `N ≥ 1` variables) there is a fixed positive integer `p` with
`N ≤ |E|`, `n, |E| ≤ N (log(N + 2))^p` and `n/2 ≤ |E| ≤ Δn/2`, where `n = |V|`.

**Formalization Note** The reduction is a string function, polynomial-time in the sense of the
published `CookPvsNP.PolyTimeComputable`, from the published CNF encoding (variable indices in
unary) to `encodeGraph`; its output *is* the encoding of the graph. A 3-CNF formula has at most
three literals per clause. `N` is the number of distinct variables occurring in the formula, and
the exponent `p` may depend on the density bound `c_s` (§4.1, p.13: "Constants may depend on
`c_s`"). `log` is binary. -/
theorem theorem_5_2 :
    ∃ (Δ : ℕ) (γ : ℚ), 1 ≤ Δ ∧ 0 < γ ∧
      ∃ f : List CookPvsNP.SatSym → List CodeSym, CookPvsNP.PolyTimeComputable f ∧
        (∀ Φ : CookPvsNP.CNF, Is3CNF Φ → ∃ G : SrcGraph,
          f (CookPvsNP.encodeCNF Φ) = encodeGraph G ∧ IsShape Δ G ∧
            (Φ.Satisfiable → IsYes G) ∧ (¬ Φ.Satisfiable → IsNo γ G)) ∧
        ∀ cs : ℝ, ∃ p : ℕ, 0 < p ∧
          ∀ (Φ : CookPvsNP.CNF) (G : SrcGraph), Is3CNF Φ →
            f (CookPvsNP.encodeCNF Φ) = encodeGraph G → 1 ≤ numVars Φ →
            (Φ.length : ℝ) ≤ cs * numVars Φ →
            numVars Φ ≤ G.edges.length ∧
            (G.n : ℝ) ≤ numVars Φ * Real.logb 2 (numVars Φ + 2) ^ p ∧
            (G.edges.length : ℝ) ≤ numVars Φ * Real.logb 2 (numVars Φ + 2) ^ p ∧
            (G.n : ℝ) / 2 ≤ G.edges.length ∧
            (G.edges.length : ℝ) ≤ Δ * G.n / 2 := by sorry

end DetCCHard
