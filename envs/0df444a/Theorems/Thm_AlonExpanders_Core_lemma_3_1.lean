-- Prove2me | Theorems.Thm_AlonExpanders_Core_lemma_3_1
-- name    : AlonExpanders.Core.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:31:51.013669+00:00
-- url     : https://prove2.me/theorems/2288e794-7b92-4669-ab1c-d906b97b1ca5
-- title:
--   Lemma 3.1 — a strong $(n, d, c)$-expander is a $(2n, d, c/16)$-magnifier
-- statement:
--   Let $G = (I, O; E)$ be a bipartite graph with $|I| = |O| = n \ge 2$, and let $c$ be a real number. If $G$ is a strong $(n, d, c)$-expander, that is
--
--   $$
--   |N(X)| \ge \Bigl(1 + c\Bigl(1 - \frac{|X|}{n}\Bigr)\Bigr)|X| \quad \text{for every } X \subseteq I,
--   $$
--
--   and every vertex has degree at most $d$, then $G$, viewed as a graph on its $2n$ vertices, is a $(2n, d, c/16)$-magnifier: every set $X \subseteq I \cup O$ with $|X| \le n$ satisfies
--
--   $$
--   |N(X) - X| \;\ge\; \frac{c}{16}\,|X|.
--   $$
--
--   The lemma converts the one-sided expansion of a bipartite graph into the two-sided vertex expansion that Lemma 2.4 turns into a spectral gap. The word "strong" cannot be dropped (remark on p. 90 of the paper).
--
--   **Formalization Note** The hypothesis $n \ge 2$ is added and necessary: for $n = 1$ the single edge $K_2$ is a strong $(1, 1, c)$-expander for every $c$, but for $c > 16$ it is not a $(2, 1, c/16)$-magnifier, since a single vertex $X$ has $|N(X) - X| = 1 < c/16$. No sign condition on $c$ is needed.
-- source:
--   Alon, Eigenvalues and expanders, Combinatorica 6 (1986), p. 90, Lemma 3.1

import Mathlib
import Definitions.Def_AlonExpanders_Core_IsStrongExpander
import Definitions.Def_AlonExpanders_Core_IsMagnifier

namespace AlonExpanders.Core

/-- Lemma 3.1 of Alon, *Eigenvalues and expanders*, Combinatorica 6 (1986), p. 90: a strong
`(n, d, c)`-expander on `I ⊕ O` is a `(2n, d, c/16)`-magnifier. The hypothesis `2 ≤ n` is added:
for `n = 1`, `K₂` is a strong `(1, 1, c)`-expander for every `c` but not a `(2, 1, c/16)`-magnifier
once `c > 16`. -/
theorem lemma_3_1 {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj] (n d : ℕ) (c : ℝ) (hn : 2 ≤ n)
    (hG : IsStrongExpander G n d c) :
    IsMagnifier G (2 * n) d (c / 16) := by sorry

end AlonExpanders.Core
