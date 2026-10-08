-- Prove2me | Theorems.Thm_AlonExpanders_Core_theorem_3_4
-- name    : AlonExpanders.Core.theorem_3_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T04:32:06.233585+00:00
-- url     : https://prove2.me/theorems/1c801ecd-9591-449c-9b6a-704cca9e7d45
-- title:
--   Theorem 3.4 — a $d$-regular bipartite graph is a strong expander iff $\lambda(G)$ is bounded away from $0$
-- statement:
--   Let $G = (I, O; E)$ be a $d$-regular bipartite graph with $|I| = |O| = n$, and let $\lambda = \lambda(G)$ be the second-smallest eigenvalue of its Laplacian $Q_G = dI - A_G$, counted with multiplicity.
--
--   1. If $n \ge 1$, $c \ge 0$ and $G$ is a strong $(n, d, c)$-expander, then
--   $$
--   \lambda \;\ge\; \frac{c^2}{1024 + 2c^2},
--   $$
--   i.e. $G$ is a $(2n, d, c^2/(1024+2c^2))$-enlarger.
--   2. If $\varepsilon > 0$ and $\lambda \ge \varepsilon$, i.e. $G$ is a $(2n, d, \varepsilon)$-enlarger, then $G$ is a strong $(n, d, c)$-expander with
--   $$
--   c = \frac{2d\varepsilon - \varepsilon^2}{d^2}.
--   $$
--
--   Here a strong $(n, d, c)$-expander is a bipartite graph with $|I| = |O| = n$ and degrees at most $d$ in which every $X \subseteq I$ satisfies $|N(X)| \ge (1 + c(1 - |X|/n))|X|$.
--
--   The theorem says that for regular bipartite graphs vertex expansion and the spectral gap of the Laplacian are equivalent, with explicit constants in both directions. Since $\lambda(G)$ is computable in polynomial time, this gives an efficient certificate of expansion, whereas deciding expansion exactly is coNP-complete.
--
--   **Formalization Note** Three hypotheses absent from the page are added, each necessary. $n \ge 1$ in (1): for $n = 0$ the graph is empty, $\lambda = 0$ by convention, and the expander condition holds vacuously. $c \ge 0$ in (1): a perfect matching on $2 + 2$ vertices is a strong $(2, 1, -1)$-expander with $\lambda = 0$. $\varepsilon > 0$ in (2): for $d = 0$ and $n \ge 1$, $\lambda = 0 \ge \varepsilon$ for every $\varepsilon \le 0$, yet the edgeless graph is no strong expander. The closing sentence of the theorem ("Thus … one can prove efficiently … $c' \ge c^2/(1032d)$") is an algorithmic remark and is not formalized. $\lambda(G)$ is the published `AlonMilman.Diameter.lambda1`, $N(X)$ the published `AKSSorting.Core.neighbours`.
-- source:
--   Alon, Eigenvalues and expanders, Combinatorica 6 (1986), pp. 92–93, Theorem 3.4 (1) and (2)

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1
import Definitions.Def_AlonExpanders_Core_IsIOBipartite
import Definitions.Def_AlonExpanders_Core_IsStrongExpander

namespace AlonExpanders.Core

/-- Theorem 3.4 of Alon, *Eigenvalues and expanders*, Combinatorica 6 (1986), pp. 92–93. Let `G`
be a `d`-regular bipartite graph on `I ⊕ O` with `|I| = |O| = n` and `λ = λ(G)`.
(1) If `G` is a strong `(n, d, c)`-expander then `λ ≥ c²/(1024 + 2c²)`.
(2) If `λ ≥ ε` then `G` is a strong `(n, d, (2dε − ε²)/d²)`-expander.
Added hypotheses: `1 ≤ n` and `0 ≤ c` in (1), `0 < ε` in (2); each is necessary (empty graph at
`n = 0`; a perfect matching is a strong `(2, 1, −1)`-expander with `λ = 0`; the empty graph with
`d = 0` has `λ = 0 ≥ ε` for `ε ≤ 0` and is no strong expander). -/
theorem theorem_3_4 {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj] (n d : ℕ)
    (hI : Fintype.card I = n) (hO : Fintype.card O = n)
    (hbip : IsIOBipartite G) (hreg : G.IsRegularOfDegree d) :
    (∀ c : ℝ, 0 ≤ c → 1 ≤ n → IsStrongExpander G n d c →
        c ^ 2 / (1024 + 2 * c ^ 2) ≤ AlonMilman.Diameter.lambda1 G) ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ AlonMilman.Diameter.lambda1 G →
        IsStrongExpander G n d ((2 * (d : ℝ) * ε - ε ^ 2) / (d : ℝ) ^ 2)) := by sorry

end AlonExpanders.Core
