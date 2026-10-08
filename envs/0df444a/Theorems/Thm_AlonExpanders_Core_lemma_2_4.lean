-- Prove2me | Theorems.Thm_AlonExpanders_Core_lemma_2_4
-- name    : AlonExpanders.Core.lemma_2_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T04:09:33.12998+00:00
-- url     : https://prove2.me/theorems/ddffa837-177d-4dfa-a0ce-8b3b7dcd2060
-- title:
--   Lemma 2.4 — every $(n, d, c)$-magnifier has $\lambda(G) \ge c^2/(4+2c^2)$
-- statement:
--   Let $G = (V, E)$ be a finite simple graph on $n \ge 2$ vertices with maximal degree at most $d$, and let $\lambda(G)$ be the second-smallest eigenvalue of its Laplacian $Q_G = \mathrm{diag}(d(v)) - A_G$. Let $c \ge 0$. If $G$ is an $(n, d, c)$-magnifier, i.e. $|N(X) - X| \ge c|X|$ for every $X \subseteq V$ with $|X| \le n/2$, then
--
--   $$
--   \lambda(G) \;\ge\; \frac{c^2}{4 + 2c^2},
--   $$
--
--   so $G$ is an $(n, d, \varepsilon)$-enlarger with $\varepsilon = c^2/(4+2c^2)$.
--
--   This is the discrete Cheeger-type inequality of the paper: vertex expansion forces a spectral gap. Together with Corollary 2.3 it shows that magnifiers and enlargers are the same graphs up to the constants.
--
--   **Formalization Note** Two hypotheses absent from the page are added, both necessary. $n \ge 2$: on one vertex the only set with $|X| \le 1/2$ is $\emptyset$, so every one-vertex graph is a $(1, 0, c)$-magnifier for every $c$, while $\lambda$ is $0$ by convention. $c \ge 0$: for $c < 0$ the magnifier condition is vacuous, and two disjoint edges form a $(4, 1, -1)$-magnifier with $\lambda = 0$.
-- source:
--   Alon, Eigenvalues and expanders, Combinatorica 6 (1986), p. 86, Lemma 2.4 (proof pp. 86–88)

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1
import Definitions.Def_AlonExpanders_Core_IsMagnifier

namespace AlonExpanders.Core

/-- Lemma 2.4 of Alon, *Eigenvalues and expanders*, Combinatorica 6 (1986), p. 86: every
`(n, d, c)`-magnifier satisfies `λ(G) ≥ c²/(4 + 2c²)`. The hypotheses `2 ≤ n` and `0 ≤ c` are
added: for `n = 1` every graph is a magnifier for every `c` while `λ = 0` by convention, and for
`c < 0` the magnifier condition is vacuous (two disjoint edges, `λ = 0`). -/
theorem lemma_2_4 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n d : ℕ) (c : ℝ) (hn : 2 ≤ n) (hc : 0 ≤ c) (hG : IsMagnifier G n d c) :
    c ^ 2 / (4 + 2 * c ^ 2) ≤ AlonMilman.Diameter.lambda1 G := by sorry

end AlonExpanders.Core
