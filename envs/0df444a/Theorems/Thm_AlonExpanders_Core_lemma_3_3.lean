-- Prove2me | Theorems.Thm_AlonExpanders_Core_lemma_3_3
-- name    : AlonExpanders.Core.lemma_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T04:31:55.237151+00:00
-- url     : https://prove2.me/theorems/389ac8fc-6609-49a9-b96c-14eafbfbe552
-- title:
--   Lemma 3.3 — a $d$-regular bipartite graph is a strong $(n, d, (2d\lambda-\lambda^2)/d^2)$-expander
-- statement:
--   Let $G = (I, O; E)$ be a $d$-regular bipartite graph with $d \ge 1$ and $|I| = |O| = n$, and let $\lambda = \lambda(G)$ be the second-smallest eigenvalue of its Laplacian $Q_G = dI - A_G$. Then $G$ is a strong $(n, d, c)$-expander with
--
--   $$
--   c = \frac{2d\lambda - \lambda^2}{d^2}:
--   $$
--
--   for every $X \subseteq I$, $|N(X)| \ge \bigl(1 + c(1 - |X|/n)\bigr)|X|$.
--
--   This is the direction "spectral gap implies expansion" of Theorem 3.4, with a constant obtained from Tanner's bound.
--
--   **Formalization Note** The hypothesis $d \ge 1$ is added and necessary: for $d = 0$ the formula divides by zero, which Lean evaluates to $c = 0$, and the edgeless graph with $n \ge 1$ does not satisfy $|N(I)| \ge |I|$. The paper's parenthetical remark "always $\lambda \le d$ and hence $c \ge \lambda/d$" is not part of the statement; it fails for $n = 1$ (the single edge $K_2$ has $\lambda = 2 > d = 1$).
-- source:
--   Alon, Eigenvalues and expanders, Combinatorica 6 (1986), p. 92, Lemma 3.3

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1
import Definitions.Def_AlonExpanders_Core_IsIOBipartite
import Definitions.Def_AlonExpanders_Core_IsStrongExpander

namespace AlonExpanders.Core

/-- Lemma 3.3 of Alon, *Eigenvalues and expanders*, Combinatorica 6 (1986), p. 92: a `d`-regular
bipartite graph on `I ⊕ O` with `|I| = |O| = n` and `λ = λ(G)` is a strong `(n, d, c)`-expander
with `c = (2dλ − λ²)/d²`. The hypothesis `1 ≤ d` is added: for `d = 0` Lean's `0/0 = 0` gives
`c = 0`, and the empty graph with `n ≥ 1` fails `|N(I)| ≥ |I|`. -/
theorem lemma_3_3 {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj] (n d : ℕ) (hd : 1 ≤ d)
    (hI : Fintype.card I = n) (hO : Fintype.card O = n)
    (hbip : IsIOBipartite G) (hreg : G.IsRegularOfDegree d) :
    IsStrongExpander G n d
      ((2 * (d : ℝ) * AlonMilman.Diameter.lambda1 G - AlonMilman.Diameter.lambda1 G ^ 2) /
        (d : ℝ) ^ 2) := by sorry

end AlonExpanders.Core
