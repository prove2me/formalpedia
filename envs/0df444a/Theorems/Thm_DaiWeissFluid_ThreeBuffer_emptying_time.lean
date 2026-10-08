-- Prove2me | Theorems.Thm_DaiWeissFluid_ThreeBuffer_emptying_time
-- name    : DaiWeissFluid.ThreeBuffer.emptying_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:47:04.310983+00:00
-- url     : https://prove2.me/theorems/976dd410-34a1-439d-ae58-bc9c36ecacda
-- title:
--   Proof of Theorem 3.1 — the three-buffer line empties by $\max\{\rho_1/(1-\rho_1), \rho_2/(1-\rho_2)\}$
-- statement:
--   Let $m_1, m_2, m_3 > 0$ satisfy (3.1), $\rho_1 = m_1 + m_3 < 1$ and $\rho_2 = m_2 < 1$, and let $(Q, T)$ be a work-conserving fluid model solution, (1.8)–(1.13), of the three-buffer line $1 \to 2 \to 1$ with initial total fluid $|Q(0)| = Q_1(0) + Q_2(0) + Q_3(0) = 1$. Then
--
--   $$
--   Q_k(t) = 0 \qquad \text{for all } k \text{ and all } t \ge \max\Big\{\frac{\rho_1}{1-\rho_1}, \frac{\rho_2}{1-\rho_2}\Big\}.
--   $$
--
--   This is the explicit emptying time obtained from the Lyapunov function $G = \max\{G_1, G_2\}$, Lemma 3.2 and Lemma 2.2; it exhibits the constant $\delta$ required by Definition 1.3.
--
--   **Formalization Note.** Indices are 0-based: $\rho_1$ is `m 0 + m 2` and $\rho_2$ is `m 1`.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 121, proof of Theorem 3.1

import Mathlib
import Definitions.Def_DaiWeissFluid_ThreeBuffer_FluidModel
import Definitions.Def_DaiWeissFluid_ThreeBuffer_Line

namespace DaiWeissFluid.ThreeBuffer

/-- Proof of Theorem 3.1, p. 121: under (3.1), every work-conserving fluid solution of the
three-buffer line with `|Q(0)| = 1` is empty from time `max{ρ₁/(1-ρ₁), ρ₂/(1-ρ₂)}` on, where
`ρ₁ = m₁ + m₃` and `ρ₂ = m₂` (0-based: `m 0 + m 2` and `m 1`). -/
theorem emptying_time (m : Fin 3 → ℝ) (hm : ∀ k, 0 < m k) (h1 : m 0 + m 2 < 1) (h2 : m 1 < 1)
    (Q T : ℝ → Fin 3 → ℝ) (hwc : (threeBuffer m).IsWorkConserving Q T)
    (hQ0 : ∑ k, Q 0 k = 1) (t : ℝ)
    (ht : max ((m 0 + m 2) / (1 - (m 0 + m 2))) (m 1 / (1 - m 1)) ≤ t) (k : Fin 3) :
    Q t k = 0 := by sorry

end DaiWeissFluid.ThreeBuffer
