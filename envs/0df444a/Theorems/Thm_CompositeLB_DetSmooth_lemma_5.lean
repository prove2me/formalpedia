-- Prove2me | Theorems.Thm_CompositeLB_DetSmooth_lemma_5
-- name    : CompositeLB.DetSmooth.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:38.631859+00:00
-- url     : https://prove2.me/theorems/be49b64b-ce1d-4471-a815-44c8c98c0941
-- title:
--   Lemma 5, p. 16 — the partial and final functions give the same constrained prox
-- statement:
--   Under the same round, indicator, orthonormality, and hidden-direction conditions as Lemma 4, for every $\beta>0$ the constrained proximal minimizers of $f_i^t$ and $f_i$ at $x$ coincide:
--
--   $$\operatorname{prox}_{f_i^t}(x,\beta)=\operatorname{prox}_{f_i}(x,\beta).$$
--
--   The minimization in both proximal maps is over the unit ball. Thus the partial oracle's prox answer is also exact for the final component.
--
--   **Formalization Note** Equality is stated pointwise as equivalence of membership in the two argmin sets. The source's displayed computation treats an unconstrained argmin, while equation (3) defines a constrained one; the conclusion remains valid on the ball. The positive parameter $\beta$ is explicit.
-- source:
--   Woodworth & Srebro, arXiv:1605.08003v3, Lemma 5, p. 16

import Mathlib
import Definitions.Def_CompositeLB_DetSmooth_Construction

namespace CompositeLB.DetSmooth

/-- Lemma 5, p. 16: equality of the exact constrained prox solutions for
every positive prox parameter. -/
theorem lemma_5 {d k : ℕ} (a : ℝ) (v : ℕ → CompositeLB.DetLip.E d) (δ : ℕ → ℝ)
    (t : ℕ) (x : CompositeLB.DetLip.E d) (ht : 1 ≤ t) (htk : t ≤ k)
    (hv : Orthonormal ℝ (fun r : Fin (k + 1) => v (r : ℕ)))
    (hδ : ∀ r, δ r = 0 ∨ δ r = 1) (hδt : δ t = 0)
    (hx : ∀ r : ℕ, t ≤ r → r ≤ k → inner ℝ x (v r) = 0) :
    ∀ β : ℝ, 0 < β → ∀ u : CompositeLB.DetLip.E d,
      BoydADMM.Prox.IsProx (Metric.closedBall (0 : CompositeLB.DetLip.E d) 1) (hardFt a k v δ t) β x u ↔
        BoydADMM.Prox.IsProx (Metric.closedBall (0 : CompositeLB.DetLip.E d) 1) (hardF a k v δ) β x u := by sorry

end CompositeLB.DetSmooth
