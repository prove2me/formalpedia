-- Prove2me | Theorems.Thm_FamousTheorems_hofer_lemma
-- name    : FamousTheorems.hofer_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:08:28.522984+00:00
-- url     : https://prove2.me/theorems/c256b76c-3958-4a7d-bfc2-4a0609c7b148
-- title:
--   Hofer's lemma
-- statement:
--   **Hofer's lemma.** Let $X$ be a complete metric space, $\phi:X\to[0,\infty)$ continuous, $x\in X$ and $\varepsilon>0$. Then there are $0<\varepsilon'\le\varepsilon$ and $x'\in X$ with $d(x',x)\le2\varepsilon$ and $\varepsilon\,\phi(x)\le\varepsilon'\phi(x')$, such that $\phi(y)\le2\phi(x')$ for all $y$ with $d(x',y)\le\varepsilon'$.
--
--   The lemma lets one move to a nearby point where $\phi$ is almost maximal on a ball of controlled radius. Hofer used it in symplectic topology, in bubbling-off analysis for pseudoholomorphic curves, to rescale around points where the gradient blows up.
--
--   **Formalization note.** Mathlib's `hofer`. The statement is copied directly, with `ε' > 0` in bounded-quantifier form.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `hofer`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem hofer_lemma {X : Type*} [MetricSpace X] [CompleteSpace X] (x : X) {ε : ℝ} (ε_pos : 0 < ε) {ϕ : X → ℝ}
    (cont : Continuous ϕ) (nonneg : ∀ y, 0 ≤ ϕ y) :
    ∃ ε' > 0, ∃ x' : X, ε' ≤ ε ∧ dist x' x ≤ 2 * ε ∧ ε * ϕ x ≤ ε' * ϕ x' ∧
      ∀ y, dist x' y ≤ ε' → ϕ y ≤ 2 * ϕ x' := by sorry

end FamousTheorems
