-- Prove2me | Theorems.Thm_DurmusULA_StrongLC_theorem_36
-- name    : DurmusULA.StrongLC.theorem_36
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:54.774663+00:00
-- url     : https://prove2.me/theorems/5147bee1-25d3-4f43-b98f-2574d7aa3e1c
-- title:
--   Theorem 36, p. 33 — under G1 and G3, ‖P_t(x,·) − P_t(y,·)‖_TV ≤ 2{(1 − ε)^{−1} + 1 + ‖x − y‖}κ^t
-- statement:
--   Let $b:\mathbb R^d\to\mathbb R^d$ satisfy **G1** ($b$ Lipschitz and $\langle b(x)-b(y),x-y\rangle\le0$ for all $x,y$) and **G3**: there are $\tilde M_s\ge1$ and $\tilde m_s>0$ with
--   $$\langle b(x)-b(y),x-y\rangle\le-\tilde m_s\|x-y\|^2\quad\text{whenever }\|x-y\|\ge\tilde M_s .$$
--   Let $(P_t)_{t\ge0}$ be the transition semigroup of $dX_t=b(X_t)dt+dB^d_t$. Then for all $\varepsilon\in(0,1)$, $t\ge0$ and $x,y\in\mathbb R^d$,
--   $$\|P_t(x,\cdot)-P_t(y,\cdot)\|_{\mathrm{TV}}\le 2\{(1-\varepsilon)^{-1}+1+\|x-y\|\}\kappa^t,\qquad \log\kappa=\frac{\tilde m_s}{2}\log(1-\varepsilon)\big(\log D(\varepsilon)-\log(1-\varepsilon)\big)^{-1},$$
--   where $D(\varepsilon)=(1+e^{\tilde m_s\omega(\varepsilon,\tilde M_s)/2})(1+\tilde M_s)$ and $\omega$ is defined in (29).
--
--   The rate $\kappa\in(0,1)$ is explicit and dimension-free. Applied to the time-changed Langevin diffusion it gives the convergence of the Langevin semigroup to $\pi$ used in Theorem 21.
--
--   **Formalization Note** Total variation is the $\sup_{|f|\le1}$ norm. $\kappa^t$ is a real power with positive base; $D(\varepsilon)\ge4>1-\varepsilon$, so the denominator of $\log\kappa$ is positive.
-- source:
--   Durmus and Moulines, Non-asymptotic convergence analysis for the Unadjusted Langevin Algorithm, arXiv:1507.05021v3, p. 33, Theorem 36; (63) p. 32; G1 p. 28; G3 p. 31; (29) p. 13

import Mathlib
import Definitions.Def_DurmusULA_StrongLC_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal RealInnerProductSpace

namespace DurmusULA.StrongLC

theorem theorem_36 (d : ℕ) (b : EthierKurtz.SDEState d → EthierKurtz.SDEState d)
    (P : ℝ≥0 → EthierKurtz.SDEState d → Measure (EthierKurtz.SDEState d))
    (hLip : ∃ K, LipschitzWith K b)
    (hmono : ∀ x y, ⟪b x - b y, x - y⟫ ≤ 0)
    (Mt mt : ℝ) (hMt : 1 ≤ Mt) (hmt : 0 < mt)
    (hG3 : ∀ x y, Mt ≤ ‖x - y‖ → ⟪b x - b y, x - y⟫ ≤ -mt * ‖x - y‖ ^ 2)
    (hP : IsDiffusionSemigroup b 1 P) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ (t : ℝ≥0) (x y : EthierKurtz.SDEState d),
      tvNorm (P t x) (P t y) ≤
        2 * ((1 - ε)⁻¹ + 1 + ‖x - y‖) * kappa36 mt Mt ε ^ (t : ℝ) := by sorry

end DurmusULA.StrongLC
