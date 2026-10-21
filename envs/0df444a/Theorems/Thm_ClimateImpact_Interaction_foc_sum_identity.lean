-- Prove2me | Theorems.Thm_ClimateImpact_Interaction_foc_sum_identity
-- name    : ClimateImpact.Interaction.foc_sum_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T08:58:30.676084+00:00
-- url     : https://prove2.me/theorems/8b373316-e154-42e2-ac7d-4cab915e4e6d
-- title:
--   §6.3, proof of Proposition 4, p. 65 — summing (40): Σ_i x^i = 2n/(2n + (n+1)ε) · Σ_i a^i
-- statement:
--   Let $n\ge1$, $\varepsilon\ge0$, and let $a,x\in\mathbb R^n$ satisfy
--   $$x^i=a^i-\frac{\varepsilon}{2n}\Big(\sum_{j=1}^n x^j+x^i\Big)\qquad(i=1,\dots,n).$$
--   Then
--   $$\sum_{i=1}^n x^i=\frac{2n}{2n+(n+1)\varepsilon}\sum_{i=1}^n a^i .$$
--
--   Applied with $a=\psi^*_t$, this is the step that decouples the first-order system (40) and yields the closed form (15).
--
--   **Formalization Note** The vector $a$ is arbitrary, which makes the statement slightly more general than the page's $a=\psi^*_t$.
-- source:
--   SSRN 3562534 (25 Jun 2021), §6.3, proof of Proposition 4, p. 65

import Mathlib

namespace ClimateImpact.Interaction

theorem foc_sum_identity (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 ≤ ε) (a x : Fin n → ℝ)
    (h : ∀ i, x i = a i - ε / (2 * n) * (∑ j, x j + x i)) :
    ∑ i, x i = 2 * n / (2 * n + (n + 1) * ε) * ∑ i, a i := by sorry

end ClimateImpact.Interaction
