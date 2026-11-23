-- Prove2me | Theorems.Thm_AlonMilman_PropertyT_Supplement_theorem_3_4
-- name    : AlonMilman.PropertyT.Supplement.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T03:34:13.432794+00:00
-- url     : https://prove2.me/theorems/b1f42295-045b-4590-90cc-17fe9a3791ab
-- title:
--   Theorem 3.4 — odd graphs, and line graphs of concentrated families of regular graphs, are concentrated
-- statement:
--   Concentrated families are those of Definition 1.2: there are constants $c > 0$, $h > 0$ with $\alpha(G_i, \rho) \le c \exp(-[h\rho/\sqrt{\operatorname{diam} G_i}])$ for every index $i$ and every $\rho > 0$.
--
--   1. **Odd graphs.** For $k \ge 1$ let $S_k$ be a set of cardinality $2k - 1$, and let $O_k$ be the odd graph on $S_k$: its vertices are the $(k-1)$-element subsets of $S_k$, two of them adjacent iff they are disjoint (and distinct). Then the family $\{O_k\}_{k=1}^{\infty}$ is concentrated.
--   2. **Line graphs.** If $\{G_i\}_{i}$ is a concentrated family of finite graphs, each of which is regular (of a degree $d_i$ that may depend on $i$), then the family $\{L(G_i)\}_i$ of their line graphs is concentrated. Here the vertices of $L(G)$ are the edges of $G$, two of them adjacent iff they are distinct and share an endpoint.
--   3. In particular, the family $\{L(O_k)\}_{k=1}^{\infty}$ is concentrated.
--
--   Together with Theorem 3.2 these give the paper's examples of concentrated families obtained from the spectral concentration estimate (Theorem 2.6).
--
--   **Formalization Note** Graphs are finite `SimpleGraph`s and $L(G)$ is Mathlib's `SimpleGraph.lineGraph`. Parts 1 and 3 hold for every choice of the sets $S_k$ (arbitrary finite types with $|S_k| = 2k - 1$), indexed by `ℕ+`; part 2 is stated for families indexed by `ℕ`. A line graph with no vertices (that of an edgeless graph) has $\alpha = 0$ by the convention of the definition.
--
--   Differences from the source:
--   - reading: Oₖ is defined for k > 1 but the family is {Oₖ}ₖ₌₁∞ → O₁ is the one-vertex graph on the (k − 1 = 0)-subsets of a 1-element set, with no edge; reason: the printed definition at k = 1 gives one vertex (∅), which is disjoint from itself; adjacency of distinct vertices only is the paper's simple-graph reading, and it agrees with the paper for every k > 1.
--   - reading: there exist constants c, h (Definition 1.2) → constants c > 0, h > 0; reason: with h ≤ 0 the bound holds for every family, so positivity is the only meaningful reading; requiring c > 0 changes nothing because α ≥ 0.
--   - reading: a concentrated family of regular graphs → each Gᵢ is regular of some degree dᵢ, which may depend on i; reason: the page does not fix the degree, so the most general reading is taken.
--   - encoding: {Gᵢ}ᵢ₌₁∞ in part (ii) → a family indexed by ℕ; reason: a shift of the index, which does not change concentration.
--   - encoding: diameter ρᵢ, ∞ for a disconnected graph, and μ undefined on a graph with no vertices → `SimpleGraph.diam` (0 for one vertex or a disconnected graph) and α = 0 on an empty vertex set; reason: hρ/√∞ = 0 on the page and hρ/√0 = 0 in Lean give the same bound; the empty line graph of an edgeless graph has no measure on the page and the convention only fixes that degenerate term.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 81, Theorem 3.4

import Mathlib
import Definitions.Def_AlonMilman_PropertyT_Supplement_concentrationFun
import Definitions.Def_AlonMilman_PropertyT_Supplement_IsConcentrated
import Definitions.Def_AlonMilman_PropertyT_Supplement_oddGraph

namespace AlonMilman.PropertyT.Supplement

/-- Theorem 3.4 (Alon–Milman 1985, p. 81).
(i) For every choice of finite sets `S_k` with `|S_k| = 2k − 1` (`k ≥ 1`), the family of odd
graphs `{O_k}_{k ≥ 1}` on `S_k` is concentrated (`O_1` is the one-vertex graph).
(ii) If `{G_i}` is a concentrated family of finite simple graphs, each of them regular, then the
family `{L(G_i)}` of their line graphs is concentrated.
In particular the family `{L(O_k)}_{k ≥ 1}` is concentrated. -/
theorem theorem_3_4 :
    (∀ (S : ℕ+ → Type) [∀ k, Fintype (S k)] [∀ k, DecidableEq (S k)],
        (∀ k, Fintype.card (S k) = 2 * (k : ℕ) - 1) →
        IsConcentrated (fun k => {A : Finset (S k) // A.card = (k : ℕ) - 1})
          (fun k => oddGraph (S k) (k : ℕ))) ∧
    (∀ (V : ℕ → Type) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
        (G : ∀ i, SimpleGraph (V i)) [∀ i, DecidableRel (G i).Adj],
        (∀ i, ∃ d : ℕ, (G i).IsRegularOfDegree d) → IsConcentrated V G →
        IsConcentrated (fun i => (G i).edgeSet) (fun i => (G i).lineGraph)) ∧
    (∀ (S : ℕ+ → Type) [∀ k, Fintype (S k)] [∀ k, DecidableEq (S k)],
        (∀ k, Fintype.card (S k) = 2 * (k : ℕ) - 1) →
        IsConcentrated (fun k => (oddGraph (S k) (k : ℕ)).edgeSet)
          (fun k => (oddGraph (S k) (k : ℕ)).lineGraph)) := by sorry

end AlonMilman.PropertyT.Supplement
