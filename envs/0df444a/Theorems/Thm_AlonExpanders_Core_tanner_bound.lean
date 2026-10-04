-- Prove2me | Theorems.Thm_AlonExpanders_Core_tanner_bound
-- name    : AlonExpanders.Core.tanner_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:08:52.294163+00:00
-- url     : https://prove2.me/theorems/30ec00ae-69df-40ab-90a4-bd6466575e52
-- title:
--   Proof of Lemma 3.3 — Tanner's bound $|N(X)| \ge d^2|X|/(\alpha(d^2-(d-\lambda)^2)+(d-\lambda)^2)$
-- statement:
--   Let $G = (I, O; E)$ be a $d$-regular bipartite graph with $|I| = |O| = n$, and let $\lambda = \lambda(G)$ be the second-smallest eigenvalue of its Laplacian. For every set of inputs $X \subseteq I$, with $\alpha = |X|/n$,
--
--   $$
--   |N(X)| \;\ge\; \frac{d^2}{\alpha\bigl(d^2 - (d-\lambda)^2\bigr) + (d-\lambda)^2}\,|X| .
--   $$
--
--   This is Tanner's eigenvalue bound on the neighbourhood size in a regular bipartite graph (Tanner 1984, Theorem 2.1), written with $(d-\lambda)^2$ in place of the second-largest eigenvalue of $C^TC$. The paper cites it in the proof of Lemma 3.3; an elementary rearrangement turns it into the strong-expander inequality of Lemma 3.3.
--
--   **Formalization Note** When the denominator vanishes ($X = \emptyset$, or $d = 0$, or $\lambda = d$ together with $\alpha = 0$), Lean's division by zero gives the left-hand side $0$, which is also the correct bound in each case. The quotient $\alpha$ is real; no size hypothesis on $n$ is needed.
-- source:
--   Alon, Eigenvalues and expanders, Combinatorica 6 (1986), p. 92, proof of Lemma 3.3, first inequality of the display after "Therefore, by [30, Theorem 2.1]"

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1
import Definitions.Def_AKSSorting_Core_IsExpander
import Definitions.Def_AlonExpanders_Core_IsIOBipartite

namespace AlonExpanders.Core

/-- Proof of Lemma 3.3 in Alon, *Eigenvalues and expanders*, Combinatorica 6 (1986), p. 92, first
inequality of the display (Tanner's bound, [30, Theorem 2.1]): for a `d`-regular bipartite graph
on `I ⊕ O` with `|I| = |O| = n`, every `X ⊆ I` with `α = |X|/n` satisfies
`|N(X)| ≥ d² / (α (d² − (d − λ)²) + (d − λ)²) · |X|`. -/
theorem tanner_bound {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj] (n d : ℕ)
    (hI : Fintype.card I = n) (hO : Fintype.card O = n)
    (hbip : IsIOBipartite G) (hreg : G.IsRegularOfDegree d) (X : Finset I) :
    (d : ℝ) ^ 2 /
        (((X.card : ℝ) / n) * ((d : ℝ) ^ 2 - ((d : ℝ) - AlonMilman.Diameter.lambda1 G) ^ 2) +
          ((d : ℝ) - AlonMilman.Diameter.lambda1 G) ^ 2) * (X.card : ℝ) ≤
      ((AKSSorting.Core.neighbours G (X.map Function.Embedding.inl)).ncard : ℝ) := by sorry

end AlonExpanders.Core
