-- Prove2me | Theorems.Thm_BalasAdditive_Convergence_finite_steps_per_iteration
-- name    : BalasAdditive.Convergence.finite_steps_per_iteration
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:34:55.947322+00:00
-- url     : https://prove2.me/theorems/4badda11-9033-44df-9fe3-d48fbd66c6b4
-- title:
--   Convergence Theorem 2(a) — only finitely many steps per iteration
-- statement:
--   Starting from any reachable state of the additive algorithm, it is impossible to keep making algorithm transitions forever while the number of generated solutions stays fixed:
--
--   $$\nexists (\sigma_t)_{t\ge0}:\ \sigma_0=\sigma,\quad \sigma_t\to\sigma_{t+1}\ (t\ge0),\quad |H(\sigma_t)|=|H(\sigma)|\ (t\ge0).$$
--
--   Here $H(\sigma)$ is the list of generated solutions. This gives precise content to part (a) of the proof: an iteration cannot repeat the older-solution scan indefinitely without either generating a new solution or stopping.
--
--   **Formalization Note** The transition relation treats repeated step-5 checks as actual transitions, so the assertion is not true by definition.
-- source:
--   Balas, An additive algorithm for solving linear programs with zero-one variables, Oper. Res. 13 (1965), p. 533, proof of Convergence Theorem 2, part (a), DOI 10.1287/opre.13.4.517

import Mathlib
import Definitions.Def_BalasAdditive_Convergence_Algorithm

set_option autoImplicit false

namespace BalasAdditive.Convergence

/-- Proof of Convergence Theorem 2, part (a), p. 533. -/
theorem finite_steps_per_iteration {n m : ℕ} (P : Problem n m) (σ : State n)
    (hr : Reachable P σ) :
    ¬ ∃ run : ℕ → State n,
      run 0 = σ ∧
      (∀ t, Step P (run t) (run (t + 1))) ∧
      (∀ t, (run t).history.length = σ.history.length) := by sorry

end BalasAdditive.Convergence
