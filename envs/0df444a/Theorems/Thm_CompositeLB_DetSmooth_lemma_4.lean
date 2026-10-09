-- Prove2me | Theorems.Thm_CompositeLB_DetSmooth_lemma_4
-- name    : CompositeLB.DetSmooth.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:44.527431+00:00
-- url     : https://prove2.me/theorems/3b813aa1-1b83-4d58-9505-9db5e98fad15
-- title:
--   Lemma 4, p. 15 — the partial and final functions give the same gradient
-- statement:
--   Let $1\le t\le k$. Suppose $v_0,\ldots,v_k$ are orthonormal, the indicators are binary, and component $i$ is queried during round $t$, so $\delta_{i,t}=0$. If $x$ has no coordinate in directions $v_t,\ldots,v_k$, then
--
--   $$\nabla f_i^t(x)=\nabla f_i(x).$$
--
--   This verifies that the adversary's gradient answer from the partial function remains an exact gradient of the final component.
--
--   **Formalization Note** Equality is expressed as equivalence of the `HasGradientAt` predicates for every candidate gradient, avoiding a default value at a nondifferentiable point. The condition $t\ge1$ reflects that rounds start at one. The proof display on p. 15 misprints the derivative of its first quadratic term; the statement uses the actual functions.
-- source:
--   Woodworth & Srebro, arXiv:1605.08003v3, Lemma 4, p. 15

import Mathlib
import Definitions.Def_CompositeLB_DetSmooth_Construction

namespace CompositeLB.DetSmooth

/-- Lemma 4, p. 15: at a point lying in the span of already exposed
directions, the partial and final component functions have the same gradient
when the component is queried during round `t`. -/
theorem lemma_4 {d k : ℕ} (a : ℝ) (v : ℕ → CompositeLB.DetLip.E d) (δ : ℕ → ℝ)
    (t : ℕ) (x : CompositeLB.DetLip.E d) (ht : 1 ≤ t) (htk : t ≤ k)
    (hv : Orthonormal ℝ (fun r : Fin (k + 1) => v (r : ℕ)))
    (hδ : ∀ r, δ r = 0 ∨ δ r = 1) (hδt : δ t = 0)
    (hx : ∀ r : ℕ, t ≤ r → r ≤ k → inner ℝ x (v r) = 0) :
    ∀ g : CompositeLB.DetLip.E d,
      HasGradientAt (hardFt a k v δ t) g x ↔
        HasGradientAt (hardF a k v δ) g x := by sorry

end CompositeLB.DetSmooth
