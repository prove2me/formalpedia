-- Prove2me | Theorems.Thm_DaiWeissFluid_ThreeBuffer_drift_rate
-- name    : DaiWeissFluid.ThreeBuffer.drift_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:46:50.131023+00:00
-- url     : https://prove2.me/theorems/b7ce7c6f-e831-4089-b7d5-f9f20ed160b1
-- title:
--   Proof of Theorem 3.1 — $\dot G_i(t) = -(1/\rho_i - 1) < 0$ while station $i$ is busy
-- statement:
--   Let $m_1, m_2, m_3 > 0$ satisfy (3.1), $\rho_1 = m_1 + m_3 < 1$ and $\rho_2 = m_2 < 1$, and let $(Q, T)$ be a work-conserving fluid model solution, (1.8)–(1.13), of the three-buffer line $1 \to 2 \to 1$, with Lyapunov components $G_1, G_2$ as in the proof of Theorem 3.1. If $t > 0$, station $i$ has positive immediate volume $W_i(t) > 0$, and $G_i$ is differentiable at $t$, then
--
--   $$
--   \dot G_i(t) = -\Big(\frac{1}{\rho_i} - 1\Big) < 0 .
--   $$
--
--   This is where work conservation enters the stability proof: a station with fluid present works at full rate, $\dot B_i(t) = 1$, so its Lyapunov component decreases at a fixed positive rate.
--
--   **Formalization Note.** Indices are 0-based (station `i : Fin 2`). Work conservation (1.13) is in the interval form of the definition module.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 121, proof of Theorem 3.1

import Mathlib
import Definitions.Def_DaiWeissFluid_ThreeBuffer_FluidModel
import Definitions.Def_DaiWeissFluid_ThreeBuffer_Line

namespace DaiWeissFluid.ThreeBuffer

/-- Proof of Theorem 3.1, p. 121: under (3.1), along every work-conserving fluid solution of the
three-buffer line, at a time `t > 0` where station `i` (0-based) has positive volume and `G_i` is
differentiable, `Ġ_i(t) = -(1/ρ_i - 1) < 0`. -/
theorem drift_rate (m : Fin 3 → ℝ) (hm : ∀ k, 0 < m k) (h1 : m 0 + m 2 < 1) (h2 : m 1 < 1)
    (Q T : ℝ → Fin 3 → ℝ) (hwc : (threeBuffer m).IsWorkConserving Q T) (i : Fin 2) (t : ℝ)
    (ht : 0 < t) (hW : 0 < (threeBuffer m).volume Q i t) (d : ℝ)
    (hd : HasDerivAt (lyap m Q i) d t) :
    d = -(1 / (threeBuffer m).ρ i - 1) ∧ d < 0 := by sorry

end DaiWeissFluid.ThreeBuffer
