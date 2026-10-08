-- Prove2me | Theorems.Thm_DaiWeissFluid_ThreeBuffer_drift_identity
-- name    : DaiWeissFluid.ThreeBuffer.drift_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:46:29.99969+00:00
-- url     : https://prove2.me/theorems/f207a4d2-9c31-4d31-b15e-b13dac397f28
-- title:
--   Proof of Theorem 3.1 — $G_i(t) = G_i(0) + t - B_i(t)/\rho_i$ on the three-buffer line
-- statement:
--   Let $m_1, m_2, m_3 > 0$ and let $(Q, T)$ be a fluid model solution, (1.8)–(1.12), of the three-buffer line $1 \to 2 \to 1$. With $\theta = m_1/(m_1+m_3)$, $G_1 = \theta Q_1^+ + (1-\theta) Q_3^+$, $G_2 = Q_2^+$, busy times $B_1 = T_1 + T_3$, $B_2 = T_2$ and workloads $\rho_1 = m_1 + m_3$, $\rho_2 = m_2$, for every $t \ge 0$
--
--   $$
--   G_1(t) = G_1(0) + t - \frac{B_1(t)}{\rho_1}, \qquad G_2(t) = G_2(0) + t - \frac{B_2(t)}{\rho_2}.
--   $$
--
--   The identity rests on $\theta\mu_1 = (1-\theta)\mu_3 = 1/\rho_1$: the Lyapunov component of each station decreases at a rate proportional to the work the station does, against a unit rate of arrivals.
--
--   **Formalization Note.** The paper writes out the identity for $G_1$ and states the one for $G_2$ by "Similarly"; both are included. Indices are 0-based (station `i : Fin 2`, `lyap m Q i`). No load condition (3.1) is needed and none is assumed.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 121, proof of Theorem 3.1

import Mathlib
import Definitions.Def_DaiWeissFluid_ThreeBuffer_FluidModel
import Definitions.Def_DaiWeissFluid_ThreeBuffer_Line

namespace DaiWeissFluid.ThreeBuffer

/-- Proof of Theorem 3.1, p. 121: along every fluid solution of the three-buffer line and for
`t ≥ 0`, `G_i(t) = G_i(0) + t - B_i(t)/ρ_i` for both Lyapunov components (0-based `i`). -/
theorem drift_identity (m : Fin 3 → ℝ) (hm : ∀ k, 0 < m k) (Q T : ℝ → Fin 3 → ℝ)
    (hsol : (threeBuffer m).IsFluidSolution Q T) (t : ℝ) (ht : 0 ≤ t) (i : Fin 2) :
    lyap m Q i t =
      lyap m Q i 0 + t - (threeBuffer m).busy T i t / (threeBuffer m).ρ i := by sorry

end DaiWeissFluid.ThreeBuffer
