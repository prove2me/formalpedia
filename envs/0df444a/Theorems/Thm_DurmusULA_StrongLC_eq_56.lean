-- Prove2me | Theorems.Thm_DurmusULA_StrongLC_eq_56
-- name    : DurmusULA.StrongLC.eq_56
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:37.350996+00:00
-- url     : https://prove2.me/theorems/1c9920fd-43df-468f-bfef-64faf5fe075a
-- title:
--   (56), p. 30 — under G1, sup_{‖x−y‖≤R} ‖P_t(x,·) − P_t(y,·)‖_TV ≤ 2(1 − ε) for t ≥ ω(ε, R)
-- statement:
--   Let $b:\mathbb R^d\to\mathbb R^d$ satisfy assumption **G1**: $b$ is Lipschitz and $\langle b(x)-b(y),x-y\rangle\le0$ for all $x,y\in\mathbb R^d$. Let $(P_t)_{t\ge0}$ be the transition semigroup of
--   $$dX_t=b(X_t)\,dt+dB^d_t .$$
--   For $R>0$ set $\Delta_R=\{(x,y):\|x-y\|\le R\}$ and let $\omega(\varepsilon,R)=R^2/\{2\Phi^{-1}(1-\varepsilon/2)\}^2$. Then for all $\varepsilon\in(0,1)$, $R>0$ and $t\ge\omega(\varepsilon,R)$,
--   $$\sup_{(x,y)\in\Delta_R}\|P_t(x,\cdot)-P_t(y,\cdot)\|_{\mathrm{TV}}\le 2(1-\varepsilon).$$
--
--   This one-step contraction on a bounded set is the building block of the explicit exponential rate of Theorem 36.
--
--   **Formalization Note** Total variation is the $\sup_{|f|\le1}$ norm of the paper (values in $[0,2]$). The supremum over $\Delta_R$ is a universal quantifier over $x,y$ with $\|x-y\|\le R$. The semigroup is pinned by the laws of all strong solutions (`IsDiffusionSemigroup b 1 P`).
-- source:
--   Durmus and Moulines, Non-asymptotic convergence analysis for the Unadjusted Langevin Algorithm, arXiv:1507.05021v3, p. 30, (56); G1 p. 28; (29) p. 13

import Mathlib
import Definitions.Def_DurmusULA_StrongLC_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal RealInnerProductSpace

namespace DurmusULA.StrongLC

theorem eq_56 (d : ℕ) (b : EthierKurtz.SDEState d → EthierKurtz.SDEState d)
    (P : ℝ≥0 → EthierKurtz.SDEState d → Measure (EthierKurtz.SDEState d))
    (hLip : ∃ K, LipschitzWith K b)
    (hmono : ∀ x y, ⟪b x - b y, x - y⟫ ≤ 0)
    (hP : IsDiffusionSemigroup b 1 P) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ R : ℝ, 0 < R → ∀ t : ℝ≥0, omega ε R ≤ (t : ℝ) →
      ∀ x y : EthierKurtz.SDEState d, ‖x - y‖ ≤ R →
        tvNorm (P t x) (P t y) ≤ 2 * (1 - ε) := by sorry

end DurmusULA.StrongLC
