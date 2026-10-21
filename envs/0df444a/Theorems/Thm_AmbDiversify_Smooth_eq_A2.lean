-- Prove2me | Theorems.Thm_AmbDiversify_Smooth_eq_A2
-- name    : AmbDiversify.Smooth.eq_A2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:09.331724+00:00
-- url     : https://prove2.me/theorems/5766b2a1-0239-4c27-b9e5-1e8afa23c950
-- title:
--   (A.2), p. 15 (PDF 16) — VD_AN = [µp1(1 − p1) + (1 − µ)p2(1 − p2)][2u(W0 − L/2) − u(W0 − L) − u(W0)]
-- statement:
--   Let $u:\mathbb R\to\mathbb R$ be any utility function, $W_0,L\in\mathbb R$, expert probabilities $p_1,p_2\in\mathbb R$ and prior weight $\mu\in\mathbb R$ (with $\mu(1)=\mu$, $\mu(2)=1-\mu$). The value of diversification under ambiguity neutrality, $VD_{AN}=EU^D_{AN}-EU^{ND}_{AN}$, satisfies
--
--   $$VD_{AN} = \big[\mu p_1(1-p_1) + (1-\mu)p_2(1-p_2)\big]\left[2u\!\left(W_0-\tfrac L2\right)-u(W_0-L)-u(W_0)\right].$$
--
--   Equivalently $VD_{AN} = \mu\Delta(1)+(1-\mu)\Delta(2)$, the prior average of the experts' values of diversification; this is the benchmark against which Proposition 4.1 compares the smooth model.
--
--   **Formalization Note** The identity is algebraic, so no hypothesis on $u$, $\mu$ or $p_\theta$ is needed.
-- source:
--   Berger & Eeckhoudt, Risk, ambiguity, and the value of diversification, iRisk Working Paper 2021-iRisk-02 (IÉSEG, April 2021), p. 15 (PDF 16), (A.2), proof of Propositions 1 and 2

import Mathlib
import Definitions.Def_AmbDiversify_Smooth_Model

namespace AmbDiversify.Smooth

/-- (A.2), proof of Propositions 1 and 2, p. 15: with `µ(1) = µ`, `µ(2) = 1 − µ`,
`VD_AN = [µp1(1 − p1) + (1 − µ)p2(1 − p2)][2u(W0 − L/2) − u(W0 − L) − u(W0)]`. -/
theorem eq_A2 (u : ℝ → ℝ) (W0 L μ p1 p2 : ℝ) :
    VD_AN u W0 L μ p1 p2 =
      (μ * p1 * (1 - p1) + (1 - μ) * p2 * (1 - p2)) *
        (2 * u (W0 - L / 2) - u (W0 - L) - u W0) := by sorry

end AmbDiversify.Smooth
