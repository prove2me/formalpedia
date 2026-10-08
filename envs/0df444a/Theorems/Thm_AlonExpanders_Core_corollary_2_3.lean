-- Prove2me | Theorems.Thm_AlonExpanders_Core_corollary_2_3
-- name    : AlonExpanders.Core.corollary_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T04:09:37.242258+00:00
-- url     : https://prove2.me/theorems/df08b885-76ad-426d-9d9d-bc384b479fd5
-- title:
--   Corollary 2.3 — every $(n, d, \varepsilon)$-enlarger is an $(n, d, 2\varepsilon/(d+2\varepsilon))$-magnifier
-- statement:
--   Let $G = (V, E)$ be a finite simple graph on $n$ vertices with maximal degree at most $d$, and let $\lambda(G)$ be the second-smallest eigenvalue of its Laplacian $Q_G = \mathrm{diag}(d(v)) - A_G$. Let $\varepsilon \ge 0$. If $G$ is an $(n, d, \varepsilon)$-enlarger, that is $\lambda(G) \ge \varepsilon$, then $G$ is an $(n, d, c)$-magnifier with
--
--   $$
--   c = \frac{2\varepsilon}{d + 2\varepsilon}:
--   $$
--
--   every set $X$ of at most $n/2$ vertices satisfies $|N(X) - X| \ge c\,|X|$.
--
--   This is one half of the equivalence between magnifiers and enlargers: a spectral gap certifies vertex expansion.
--
--   **Formalization Note** The hypothesis $\varepsilon \ge 0$ is not on the page and is necessary: with $d = 0$ and $\varepsilon = -1$ the formula gives $c = 1$, and an edgeless graph on $n \ge 2$ vertices is an $(n, 0, -1)$-enlarger but not an $(n, 0, 1)$-magnifier. The paper's enlargers have $\varepsilon > 0$; for $\varepsilon = 0$ the claim holds with $c = 0$.
-- source:
--   Alon, Eigenvalues and expanders, Combinatorica 6 (1986), p. 85, Corollary 2.3 (proof p. 86)

import Mathlib
import Definitions.Def_AlonExpanders_Core_IsEnlarger
import Definitions.Def_AlonExpanders_Core_IsMagnifier

namespace AlonExpanders.Core

/-- Corollary 2.3 of Alon, *Eigenvalues and expanders*, Combinatorica 6 (1986), p. 85: every
`(n, d, ε)`-enlarger is an `(n, d, c)`-magnifier with `c = 2ε/(d + 2ε)`. The hypothesis `0 ≤ ε`
is added: with `d = 0`, `ε = −1` one gets `c = 1`, and an edgeless graph on `n ≥ 2` vertices is an
`(n, 0, −1)`-enlarger but not an `(n, 0, 1)`-magnifier. -/
theorem corollary_2_3 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n d : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hG : IsEnlarger G n d ε) :
    IsMagnifier G n d (2 * ε / ((d : ℝ) + 2 * ε)) := by sorry

end AlonExpanders.Core
