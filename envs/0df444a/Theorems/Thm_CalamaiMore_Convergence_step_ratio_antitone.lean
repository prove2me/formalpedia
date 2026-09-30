-- Prove2me | Theorems.Thm_CalamaiMore_Convergence_step_ratio_antitone
-- name    : CalamaiMore.Convergence.step_ratio_antitone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:31:54.750088+00:00
-- url     : https://prove2.me/theorems/0d331c6b-d3bb-424f-a5c8-a94d4dec46fb
-- title:
--   Lemma 2.2 — $\|P(x + \alpha d) - x\|/\alpha$ is nonincreasing
-- statement:
--   Let $\Omega$ be a nonempty closed convex subset of a finite-dimensional real inner product space $E$ and $P$ the projection into $\Omega$. Given $x \in E$ and $d \in E$, the function
--
--   $$
--   \psi(\alpha) = \frac{\|P(x + \alpha d) - x\|}{\alpha}, \qquad \alpha > 0,
--   $$
--
--   is antitone (nonincreasing) on $(0, \infty)$.
--
--   This result, due to Gafni and Bertsekas, compares the projected steps for two different step sizes along the same direction; it is the key tool for handling steps $\alpha_k$ that are not bounded away from zero.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 98, Lemma 2.2

import Mathlib
import Definitions.Def_CalamaiMore_Convergence_proj

namespace CalamaiMore.Convergence

/-- Calamai–Moré, Lemma 2.2 (p. 98): for any `x d`, the function
`ψ(α) = ‖P(x + α d) - x‖ / α` is nonincreasing on `α > 0`. -/
theorem step_ratio_antitone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Ω : Set E) (hΩne : Ω.Nonempty) (hΩc : IsClosed Ω) (hΩcv : Convex ℝ Ω)
    (x d : E) :
    AntitoneOn (fun a : ℝ => ‖proj Ω (x + a • d) - x‖ / a) (Set.Ioi 0) := by sorry

end CalamaiMore.Convergence
