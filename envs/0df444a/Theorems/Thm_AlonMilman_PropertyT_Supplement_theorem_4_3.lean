-- Prove2me | Theorems.Thm_AlonMilman_PropertyT_Supplement_theorem_4_3
-- name    : AlonMilman.PropertyT.Supplement.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T03:36:15.936886+00:00
-- url     : https://prove2.me/theorems/a6263b6f-24a8-4196-9457-39fc43654957
-- title:
--   Theorem 4.3 — the extended double cover of an $(n,k,\varepsilon)$-enlarger is an $(n,k+1,4\varepsilon/(k+4\varepsilon))$-expander
-- statement:
--   Let $\varepsilon > 0$ and let $G = (V, E)$ be an $(n, k, \varepsilon)$-enlarger: a $k$-regular graph (parallel edges and loops allowed) on $n$ vertices whose matrix $Q_G = \operatorname{diag}(d(v)) - A_G$ has second-smallest eigenvalue $\lambda_1(G) \ge \varepsilon$. Let $H$ be the extended double cover of $G$, the bipartite graph on inputs $\{x_v\}$ and outputs $\{y_w\}$, $v, w \in V$, with $x_v y_w$ an edge iff $v = w$ or $vw \in E$. Then $H$ is an $(n, k+1, c)$-expander for
--
--   $$c = \frac{4\varepsilon}{k + 4\varepsilon}:$$
--
--   $H$ has $n$ inputs, $n$ outputs and at most $(k+1)n$ edges, and every set $A$ of inputs satisfies $|N(A)| \ge \big(1 + c(1 - |A|/n)\big)|A|$.
--
--   Since $\lambda_1(G)$ can be computed efficiently while expansion cannot, the theorem turns a family of linear enlargers (such as the one of Theorem 4.9) into a family of linear expanders, and hence of linear superconcentrators.
--
--   **Formalization Note** The enlarger is the published `AlonMilman.PropertyT.IsEnlarger` (a symmetric multiplicity matrix, $k$-regular row sums, $\lambda_1 \ge \varepsilon$). The cover is given by its edge set; $N(A)$ counts distinct outputs.
--
--   Differences from the source:
--   - reading: Theorem 4.3 states no sign for ε → ε > 0; reason: Section 4 works with ε > 0 throughout ("for some fixed k and ε > 0", p. 84, Remark 4.4; c > 0 on p. 82), and for ε < 0 the printed claim fails: a perfect matching on 4 vertices is a (4, 1, −1)-enlarger, c = −4/(1 − 4) = 4/3, and the input set A = {x_u, x_v} of one matched pair has |N(A)| = 2 < (1 + (4/3)(1/2))·2.
--   - reading: a graph G = (V, E) → a finite multigraph given by a symmetric multiplicity matrix, with vᵢvⱼ ∈ E meaning at least one edge; reason: this is the published enlarger definition, matching the paper's own use of Definition 4.1 for Cayley multigraphs in Lemma 4.8; parallel edges give one edge of H.
--   - encoding: the bipartite graph H → its edge set, a set of (input, output) pairs with inputs and outputs two copies of V; reason: same graph; edges and neighbours are counted without multiplicity, as for the simple bipartite graph of Definition 4.2.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), pp. 83–84, Theorem 4.3

import Mathlib
import Definitions.Def_AlonMilman_PropertyT_IsEnlarger
import Definitions.Def_AlonMilman_PropertyT_Supplement_extendedDoubleCover
import Definitions.Def_AlonMilman_PropertyT_Supplement_IsExpander

namespace AlonMilman.PropertyT.Supplement

/-- Theorem 4.3 (Alon–Milman 1985, p. 83). Let `G = (V, E)` be an `(n, k, ε)`-enlarger with
`ε > 0` (a `k`-regular, possibly multi-, graph on `n` vertices with `λ₁(G) ≥ ε`) and let `H` be
its extended double cover. Then `H` is an `(n, k + 1, c)`-expander for `c = 4ε / (k + 4ε)`. -/
theorem theorem_4_3 {V : Type} [Fintype V] [DecidableEq V] (n k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (M : Matrix V V ℕ) (hM : AlonMilman.PropertyT.IsEnlarger n k ε M) :
    IsExpander n (k + 1) (4 * ε / ((k : ℝ) + 4 * ε)) (extendedDoubleCover M) := by sorry

end AlonMilman.PropertyT.Supplement
