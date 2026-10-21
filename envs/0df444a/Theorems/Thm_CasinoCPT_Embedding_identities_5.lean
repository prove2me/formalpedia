-- Prove2me | Theorems.Thm_CasinoCPT_Embedding_identities_5
-- name    : CasinoCPT.Embedding.identities_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:37.130069+00:00
-- url     : https://prove2.me/theorems/197f2fe8-5c5c-45e2-ac9e-8e0826ba3991
-- title:
--   (5), p. 13 — µ({x}) and U_µ(x) in terms of the potential and the tail of µ
-- statement:
--   Let $\mu\in\mathcal P_0(\mathbb Z)$ be a centred probability law on the integers with finite first moment, and let $U_\mu(x)=\int|x-y|\,\mu(dy)$ be its potential. For every integer $x$,
--   $$\mu(\{x\})=\frac{U_\mu(x+1)+U_\mu(x-1)}{2}-U_\mu(x),\qquad U_\mu(x)=-2x\,\mu([x,\infty))+x+2\sum_{y\ge x}y\,\mu(\{y\}).$$
--
--   The first identity recovers the law from its potential; the second expresses the potential through the upper tail of $\mu$. Both are used throughout the proof of Theorem 3.1 to translate between probabilities of the stopped walk and its potential.
--
--   **Formalization Note.** The sum over $y\ge x$ is a `tsum` over all integers of $y\,\mu(\{y\})$ restricted to $y\ge x$; it converges because $\mu$ has a finite first moment.
-- source:
--   Hu, Obłój & Zhou, When to Quit Gambling, if You Must!, arXiv:2102.03157v1, p. 13, (5)

import Mathlib
import Definitions.Def_CasinoCPT_Embedding_Model

namespace CasinoCPT.Embedding

open MeasureTheory ProbabilityTheory

/-- (5), p. 13: for a law `μ ∈ 𝒫₀(ℤ)` and an integer `x`,
`μ({x}) = (U_μ(x+1) + U_μ(x-1))/2 - U_μ(x)` and
`U_μ(x) = -2xμ([x,∞)) + x + 2 ∑_{y ≥ x} y μ({y})`. -/
theorem identities_5 (μ : Measure ℤ) (hμ : InP0Z μ) (x : ℤ) :
    (μ {x}).toReal =
        (potential μ ((x : ℝ) + 1) + potential μ ((x : ℝ) - 1)) / 2 - potential μ (x : ℝ) ∧
      potential μ (x : ℝ) =
        -2 * (x : ℝ) * (μ (Set.Ici x)).toReal + (x : ℝ) +
          2 * ∑' y : ℤ, (if x ≤ y then (y : ℝ) * (μ {y}).toReal else 0) := by sorry

end CasinoCPT.Embedding
