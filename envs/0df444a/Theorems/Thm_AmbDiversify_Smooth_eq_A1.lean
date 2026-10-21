-- Prove2me | Theorems.Thm_AmbDiversify_Smooth_eq_A1
-- name    : AmbDiversify.Smooth.eq_A1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:07.683673+00:00
-- url     : https://prove2.me/theorems/6a7de85f-8328-4fdf-a36e-5abc86b35249
-- title:
--   (A.1), p. 15 (PDF 16) — VD_risk = p(1 − p)[2u(W0 − L/2) − u(W0 − L) − u(W0)]
-- statement:
--   Let $u:\mathbb R\to\mathbb R$ be any utility function, $W_0, L\in\mathbb R$ and $p\in\mathbb R$. The value of diversification under risk, $VD_{risk} = EU^D - EU^{ND}$, has the closed form
--
--   $$VD_{risk} = p(1-p)\left[2u\!\left(W_0-\tfrac L2\right) - u(W_0-L) - u(W_0)\right].$$
--
--   This identity separates the probability factor $p(1-p)$ from the utility factor, a midpoint-concavity gap of $u$; it is the basis of Proposition 1 and, at $p=p_\theta$, of the expert-wise values $\Delta(\theta)$ used in the proof of Proposition 4.1.
--
--   **Formalization Note** The identity is algebraic, so no hypothesis on $u$, $L$ or $p$ is needed.
-- source:
--   Berger & Eeckhoudt, Risk, ambiguity, and the value of diversification, iRisk Working Paper 2021-iRisk-02 (IÉSEG, April 2021), p. 15 (PDF 16), (A.1), proof of Propositions 1 and 2

import Mathlib
import Definitions.Def_AmbDiversify_Smooth_Model

namespace AmbDiversify.Smooth

/-- (A.1), proof of Propositions 1 and 2, p. 15: the value of diversification under risk is
`p(1 − p)[2u(W0 − L/2) − u(W0 − L) − u(W0)]`. -/
theorem eq_A1 (u : ℝ → ℝ) (W0 L p : ℝ) :
    VD_risk u W0 L p = p * (1 - p) * (2 * u (W0 - L / 2) - u (W0 - L) - u W0) := by sorry

end AmbDiversify.Smooth
