-- Prove2me | Theorems.Thm_BalkemaDeHaan_FiniteT_sigma_pos_decreasing
-- name    : BalkemaDeHaan.FiniteT.sigma_pos_decreasing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:06:41.670217+00:00
-- url     : https://prove2.me/theorems/8137c504-c26b-4873-a336-e1ca6864c4fd
-- title:
--   Proof of Lemma 4 — σ(u) = u^{−2}(e^{−u} − 1 + u) = ∫₀¹∫₀ᵗ e^{−us} ds dt is positive and decreasing
-- statement:
--   Let
--   $$
--   \sigma(u) = \int_0^1 \int_0^t e^{-us}\, ds\, dt \qquad (u \in \mathbb R).
--   $$
--   Then
--
--   1. $\sigma(u) = u^{-2}(e^{-u} - 1 + u)$ for every $u \ne 0$;
--   2. $\sigma(u) > 0$ for every real $u$;
--   3. $\sigma$ is strictly decreasing on $\mathbb R$.
--
--   This is the elementary inequality behind Lemma 4: it bounds the derivative of $\Pi_{0,c}(x)$ in the parameter $c$.
--
--   **Formalization Note** The paper says "decreasing"; its next sentence uses the strict inequality $\sigma(u) < \sigma(-\psi)$ for $u > -\psi$, so strict decrease is stated.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 803 (PDF 12), proof of Lemma 4

import Mathlib
import Definitions.Def_BalkemaDeHaan_FiniteT_Pi0

namespace BalkemaDeHaan.FiniteT

/-- Proof of Lemma 4, p. 803: `σ(u) = u⁻²(e^{-u} - 1 + u) = ∫₀¹ ∫₀ᵗ e^{-u s} ds dt` (for `u ≠ 0`)
is positive and (strictly) decreasing in `u`. -/
theorem sigma_pos_decreasing :
    (∀ u : ℝ, u ≠ 0 → sigma u = (u ^ 2)⁻¹ * (Real.exp (-u) - 1 + u)) ∧
      (∀ u : ℝ, 0 < sigma u) ∧ StrictAnti sigma := by sorry

end BalkemaDeHaan.FiniteT
