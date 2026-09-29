-- Prove2me | Theorems.Thm_CalibratedCE_Convergence_Mp_subset_Mb
-- name    : CalibratedCE.Convergence.Mp_subset_Mb
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:29:55.098213+00:00
-- url     : https://prove2.me/theorems/13ad0db3-e05d-4e48-b039-ea8819ca34d4
-- title:
--   Proof of Theorem 1 (p. 45): $M_p(x) \subseteq M_b(x)$
-- statement:
--   Let $G = (u_1, u_2)$ be a finite two-player game and let $R_1$ be a best-reply function of player 1 (for every mixture $p$ over $S(2)$, $R_1(p)$ maximizes $\sum_y p_y u_1(\cdot, y)$). For every $x \in S(1)$,
--   $$M_p(x) = \{ p \in \Delta(S(2)) : R_1(p) = x \} \subseteq M_b(x),$$
--   where $M_b(x)$ is the set of mixtures to which $x$ is a best response.
--
--   In words: whenever player 1 actually plays $x$ in response to a forecast, $x$ is a best response to that forecast. This is the only place the proof of Theorem 1 uses that players best-respond.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 45, proof of Theorem 1

import Mathlib
import Definitions.Def_CalibratedCE_Convergence_Game
import Definitions.Def_CalibratedCE_Convergence_BestReply

namespace CalibratedCE.Convergence

/-- Proof of Theorem 1, p. 45: since player 1 plays best responses, `M_p(x) ⊆ M_b(x)`. -/
theorem Mp_subset_Mb {m n : ℕ} (u₁ : Fin m → Fin n → ℝ) (R₁ : (Fin n → ℝ) → Fin m)
    (hR₁ : IsBestReply₁ u₁ R₁) (a : Fin m) :
    Mp R₁ a ⊆ Mb u₁ a := by sorry

end CalibratedCE.Convergence
