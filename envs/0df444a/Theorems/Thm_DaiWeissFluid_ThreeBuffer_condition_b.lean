-- Prove2me | Theorems.Thm_DaiWeissFluid_ThreeBuffer_condition_b
-- name    : DaiWeissFluid.ThreeBuffer.condition_b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:47:11.784982+00:00
-- url     : https://prove2.me/theorems/493167fa-5a30-4542-8529-d6015c996325
-- title:
--   Proof of Theorem 3.1 — an empty station has the smaller Lyapunov component (condition (b) of Lemma 3.2)
-- statement:
--   Let $m_1, m_2, m_3 > 0$ and let $(Q, T)$ be a fluid model solution, (1.8)–(1.12), of the three-buffer line $1 \to 2 \to 1$, with $G_1 = \theta Q_1^+ + (1-\theta)Q_3^+$, $G_2 = Q_2^+$ and $\theta = m_1/(m_1+m_3)$. For every $t \ge 0$:
--
--   1. if $W_1(t) = 0$ then $G_1(t) = (1-\theta) Q_2^+(t) \le G_2(t)$;
--   2. if $W_2(t) = 0$ then $G_2(t) = Q_1^+(t) \le Q_1^+(t) + (1-\theta) Q_3(t) = G_1(t)$.
--
--   Together these verify condition (b) of Lemma 3.2 for the three-buffer line.
--
--   **Formalization Note.** The paper prints "$Q_1^+(t) + (1+\theta)Q_3(t) = G_1(t)$"; the intended reading, forced by the definition of $G_1$ when $Q_2(t) = 0$, is $(1-\theta)Q_3(t)$. The Lean statement asserts only the two inequalities $G_1(t) \le G_2(t)$ and $G_2(t) \le G_1(t)$ under the respective emptiness hypotheses. Indices are 0-based (stations `0`, `1`; components `lyap m Q 0`, `lyap m Q 1`).
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 121, proof of Theorem 3.1

import Mathlib
import Definitions.Def_DaiWeissFluid_ThreeBuffer_FluidModel
import Definitions.Def_DaiWeissFluid_ThreeBuffer_Line

namespace DaiWeissFluid.ThreeBuffer

/-- Proof of Theorem 3.1, p. 121: along every fluid solution of the three-buffer line and for
`t ≥ 0`, an empty station 1 gives `G₁(t) ≤ G₂(t)` and an empty station 2 gives `G₂(t) ≤ G₁(t)`
(0-based: stations `0`, `1`, components `lyap m Q 0`, `lyap m Q 1`). -/
theorem condition_b (m : Fin 3 → ℝ) (hm : ∀ k, 0 < m k) (Q T : ℝ → Fin 3 → ℝ)
    (hsol : (threeBuffer m).IsFluidSolution Q T) (t : ℝ) (ht : 0 ≤ t) :
    ((threeBuffer m).volume Q 0 t = 0 → lyap m Q 0 t ≤ lyap m Q 1 t) ∧
      ((threeBuffer m).volume Q 1 t = 0 → lyap m Q 1 t ≤ lyap m Q 0 t) := by sorry

end DaiWeissFluid.ThreeBuffer
