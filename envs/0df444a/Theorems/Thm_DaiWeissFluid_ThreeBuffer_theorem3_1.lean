-- Prove2me | Theorems.Thm_DaiWeissFluid_ThreeBuffer_theorem3_1
-- name    : DaiWeissFluid.ThreeBuffer.theorem3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:47:08.964903+00:00
-- url     : https://prove2.me/theorems/1f587f30-0bc1-453e-b8c9-60fb7dddf5d2
-- title:
--   Theorem 3.1 — every work-conserving fluid model of the three-buffer line is stable under (3.1)
-- statement:
--   Consider the three-buffer two-station reentrant line $1 \to 2 \to 1$ of Figure 1: classes $1$ and $3$ are served at station $1$, class $2$ at station $2$, with mean service times $m_1, m_2, m_3 > 0$. Assume the load condition (3.1)
--
--   $$
--   \rho_1 = m_1 + m_3 < 1 \qquad \text{and} \qquad \rho_2 = m_2 < 1 .
--   $$
--
--   Then the work-conserving fluid model (1.8)–(1.13) of this line is stable in the sense of Definition 1.3: there is $\delta > 0$ such that every work-conserving fluid model solution with $|Q(0)| = 1$ satisfies $Q_k(t) = 0$ for all $k$ and all $t \ge \delta$.
--
--   Since the fluid model of every work-conserving queueing discipline satisfies (1.8)–(1.13) plus further discipline-specific conditions, the theorem gives stability of the fluid model "for every work conserving policy" at once, and, through the paper's Theorem 1.1 (cited from Dai 1995) and its distributional assumptions, positive Harris recurrence of the corresponding queueing network under any such policy.
--
--   **Formalization Note.** Indices are 0-based: `threeBuffer m` has station map `![0, 1, 0]`, and (3.1) reads `m 0 + m 2 < 1`, `m 1 < 1`. The positivity $m_k > 0$, implicit in the paper (the $m_k$ are means of service times and $\mu_k = 1/m_k$), is an explicit hypothesis. Work conservation (1.13) is encoded in interval form; see the definition module.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 120, Theorem 3.1 and (3.1)

import Mathlib
import Definitions.Def_DaiWeissFluid_ThreeBuffer_FluidModel
import Definitions.Def_DaiWeissFluid_ThreeBuffer_Line

namespace DaiWeissFluid.ThreeBuffer

/-- Theorem 3.1, p. 120: for the three-buffer two-station reentrant line `1 → 2 → 1`, if (3.1)
`ρ₁ = m₁ + m₃ < 1` and `ρ₂ = m₂ < 1` holds, the work-conserving fluid model (1.8)–(1.13) is
stable (Definition 1.3). 0-based: `m 0 + m 2 < 1`, `m 1 < 1`. -/
theorem theorem3_1 (m : Fin 3 → ℝ) (hm : ∀ k, 0 < m k) (h1 : m 0 + m 2 < 1) (h2 : m 1 < 1) :
    FluidStable (threeBuffer m).IsWorkConserving := by sorry

end DaiWeissFluid.ThreeBuffer
