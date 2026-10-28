-- Prove2me | Theorems.Thm_DirectFidelity_RandomState_eq_38
-- name    : DirectFidelity.RandomState.eq_38
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:45.627951+00:00
-- url     : https://prove2.me/theorems/baae0e75-a13e-43ac-bbc3-fbb03d4c8262
-- title:
--   (38), p. 7 — Pr[(32) fails for some k] ≤ 4 exp(2 log d − C₁τ²(log d)/4) = 4 exp(−2 log d) = 4/d²
-- statement:
--   Let $d = 2^n$, $\tau = \sqrt{72\pi^3}$ and $C_1 = 2/(9\pi^3)$. If $\psi$ is uniformly distributed on the unit sphere of $\mathbb C^d$, then
--   $$\Pr\Bigl[\exists\, W_k \ne I:\ |\langle\psi|W_k|\psi\rangle| > \tau\sqrt{\log d}/\sqrt d\Bigr] \le 4\exp\bigl(2\log d - C_1\tau^2(\log d)/4\bigr) = 4\exp(-2\log d) = 4/d^2 .$$
--
--   The event on the left is "condition (32) of Lemma 1 fails for some $k$". The bound is the union bound over the fewer than $d^2$ non-identity labels of (37).
--
--   **Formalization Note** "(32) fails" is the strict inequality, the negation of (32). The two equalities of the printed chain are part of the statement; they hold because $C_1\tau^2/4 = 4$.
-- source:
--   Flammia and Liu, Direct fidelity estimation from few Pauli measurements, arXiv:1104.4695v3, p. 7, eq. (38)

import Mathlib
import Definitions.Def_DirectFidelity_RandomState_Setting

namespace DirectFidelity.RandomState

open MeasureTheory

theorem eq_38 (n : ℕ) :
    (unifSphere n).real
        {ψ | ∃ k : DirectFidelity.State.P n, k ≠ (fun _ => 0) ∧
          tau * Real.sqrt (Real.log (DirectFidelity.State.dim n)) / Real.sqrt (DirectFidelity.State.dim n) < ‖pauliExp k (ψ : E n)‖} ≤
        4 * Real.exp (2 * Real.log (DirectFidelity.State.dim n) - C1 * tau ^ 2 * Real.log (DirectFidelity.State.dim n) / 4) ∧
      4 * Real.exp (2 * Real.log (DirectFidelity.State.dim n) - C1 * tau ^ 2 * Real.log (DirectFidelity.State.dim n) / 4) =
        4 * Real.exp (-(2 * Real.log (DirectFidelity.State.dim n))) ∧
      4 * Real.exp (-(2 * Real.log (DirectFidelity.State.dim n))) = 4 / DirectFidelity.State.dim n ^ 2 := by sorry
end DirectFidelity.RandomState
