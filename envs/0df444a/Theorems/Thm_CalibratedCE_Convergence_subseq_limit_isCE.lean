-- Prove2me | Theorems.Thm_CalibratedCE_Convergence_subseq_limit_isCE
-- name    : CalibratedCE.Convergence.subseq_limit_isCE
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:33:03.552539+00:00
-- url     : https://prove2.me/theorems/c7ed0337-f34c-4a2d-97af-73f49867e36b
-- title:
--   Proof of Theorem 1 (p. 44): every subsequential limit of $D_t$ is a correlated equilibrium
-- statement:
--   Let $G = (u_1, u_2)$ be a finite two-player game. Suppose:
--
--   1. $R_1, R_2$ are best-reply functions of players 1 and 2 (stationary and deterministic: functions of the forecast alone);
--   2. player 1 issues forecasts $f_1(s)$, probability vectors over $S(2)$, and player 2 issues forecasts $f_2(s)$, probability vectors over $S(1)$;
--   3. the plays are $x(s) = R_1(f_1(s))$ and $y(s) = R_2(f_2(s))$;
--   4. $f_1$ is calibrated with respect to $y$, and $f_2$ is calibrated with respect to $x$.
--
--   Let $D_t$ be the empirical joint distribution of $(x, y)$. If $t_1 < t_2 < \cdots$ and $D$ are such that $D_{t_i}(a, b) \to D(a, b)$ for all $a, b$ (equivalently $\sum_{a, b} |D_{t_i}(a, b) - D(a, b)| \to 0$), then
--   $$D \in \pi(G),$$
--   i.e. $D$ is a correlated equilibrium of $G$.
--
--   Combined with compactness of the simplex, this yields Theorem 1.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 44, proof of Theorem 1

import Mathlib
import Definitions.Def_CalibratedCE_Convergence_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Convergence_BestReply
import Definitions.Def_CalibratedCE_Convergence_EmpDist

open Filter Topology

namespace CalibratedCE.Convergence

/-- Proof of Theorem 1, p. 44: under the hypotheses of Theorem 1, every subsequential limit of
the empirical joint distributions is a correlated equilibrium. -/
theorem subseq_limit_isCE {m n : ℕ}
    (u₁ u₂ : Fin m → Fin n → ℝ)
    (R₁ : (Fin n → ℝ) → Fin m) (R₂ : (Fin m → ℝ) → Fin n)
    (hR₁ : IsBestReply₁ u₁ R₁) (hR₂ : IsBestReply₂ u₂ R₂)
    (f₁ : ℕ → Fin n → ℝ) (f₂ : ℕ → Fin m → ℝ)
    (hf₁ : ∀ t, IsDist (f₁ t)) (hf₂ : ∀ t, IsDist (f₂ t))
    (hcal₁ : Shared.Calibrated f₁ (fun s => R₂ (f₂ s)))
    (hcal₂ : Shared.Calibrated f₂ (fun s => R₁ (f₁ s)))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (D : Fin m → Fin n → ℝ)
    (hD : ∀ a b, Tendsto (fun i => empDist (fun s => R₁ (f₁ s)) (fun s => R₂ (f₂ s)) (φ i) a b)
      atTop (𝓝 (D a b))) :
    IsCE u₁ u₂ D := by sorry

end CalibratedCE.Convergence
