-- Prove2me | Theorems.Thm_FixedPointAA_Main_success_probability
-- name    : FixedPointAA.Main.success_probability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:02:09.099407+00:00
-- url     : https://prove2.me/theorems/66c57d6b-60e2-4ccd-b4cf-df49b2218c05
-- title:
--   Eq. (1), p. 1 — exact success probability for the phases (11)
-- statement:
--   Let $s,T$ be unit vectors in a finite-dimensional complex state space, with $\lambda=|\langle T|s\rangle|^2>0$. Choose $l\ge0$, $L=2l+1$, and $0<\delta\le1$. Apply $G(\alpha_1,\beta_1)$ first and $G(\alpha_l,\beta_l)$ last, with the phases of Eq. (11), where $\gamma^{-1}=T_{1/L}(1/\delta)$. The exact success probability is
--
--   $$|\langle T|\mathcal S_L|s\rangle|^2=1-\delta^2T_L\!\left(T_{1/L}(1/\delta)\sqrt{1-\lambda}\right)^2.$$
--
--   This is the paper's central fixed-point amplitude-amplification formula. The equality includes $l=0$, when $\mathcal S_1$ is the identity and the probability is $\lambda$.
--
--   **Formalization Note** The statement uses the generalized reflection operators of Eqs. (6)–(7) on an arbitrary finite-dimensional space. It assumes $\delta>0$ because the fractional-order expression is a limit at $\delta=0$.
-- source:
--   Yoder, Low, Chuang, Fixed-point quantum search with an optimal number of queries, arXiv:1409.3305v2, p. 1, Eq. (1); p. 3, Eqs. (10)–(11)

import Mathlib
import Definitions.Def_FixedPointAA_Main_Setting

namespace FixedPointAA.Main
open scoped Matrix

/-- Eq. (1), with the operator sequence (10) and the phases (11). -/
theorem success_probability {N : ℕ} (s T : Fin N → ℂ)
    (hs : star s ⬝ᵥ s = 1) (hT : star T ⬝ᵥ T = 1)
    (lam : ℝ) (hlam : ‖star T ⬝ᵥ s‖ ^ 2 = lam) (hlam0 : 0 < lam)
    (l : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ‖star T ⬝ᵥ (seqOp s T (alpha l δ) (beta l δ) l *ᵥ s)‖ ^ 2 =
      PL (2 * l + 1) lam δ := by sorry

end FixedPointAA.Main
