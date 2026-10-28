-- Prove2me | Theorems.Thm_DirectFidelity_RandomState_eq_34
-- name    : DirectFidelity.RandomState.eq_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:39.029878+00:00
-- url     : https://prove2.me/theorems/d6909dd9-a6cf-4fcf-9def-e91af7042bb4
-- title:
--   (34), p. 7 — Pr[|⟨φ|ψ⟩| ≥ ε] ≤ 4 exp(−C₁dε²/η²) with η = 1, C₁ = 2/(9π³)
-- statement:
--   Let $n \ge 0$, $d = 2^n$, let $\varphi \in \mathbb C^d$ be a unit vector and $\varepsilon > 0$. If $\psi$ is uniformly distributed on the unit sphere of $\mathbb C^d$, then
--   $$\Pr\bigl[\,|\langle\varphi|\psi\rangle| \ge \varepsilon\,\bigr] \le 4\exp\!\bigl(-C_1 d\varepsilon^2/\eta^2\bigr),\qquad \eta = 1,\quad C_1 = \frac{2}{9\pi^3}.$$
--
--   In the paper this is Levy's lemma applied to the $1$-Lipschitz function of (33), whose mean is $0$. It is the per-state tail bound behind the union bound (35).
--
--   **Formalization Note** The Lipschitz coefficient $\eta = 1$ is kept visible as $1^2$ in the exponent. Here $\varepsilon$ is an arbitrary positive number; Lemma 1's specific $\varepsilon = \sqrt{9\pi^3(\log 2)c}$ enters in (35). The probability is the real-valued measure of the event under the normalised sphere measure.
-- source:
--   Flammia and Liu, Direct fidelity estimation from few Pauli measurements, arXiv:1104.4695v3, p. 7, eq. (34)

import Mathlib
import Definitions.Def_DirectFidelity_RandomState_Setting

namespace DirectFidelity.RandomState

open MeasureTheory

theorem eq_34 (n : ℕ) (φ : E n) (hφ : ‖φ‖ = 1) (ε : ℝ) (hε : 0 < ε) :
    (unifSphere n).real {ψ | ε ≤ ‖inner ℂ φ (ψ : E n)‖} ≤
      4 * Real.exp (-C1 * DirectFidelity.State.dim n * ε ^ 2 / 1 ^ 2) := by sorry
end DirectFidelity.RandomState
