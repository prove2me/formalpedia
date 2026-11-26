-- Prove2me | Theorems.Thm_ChandrasekaranNullCone_boost_mismatch_D21
-- name    : ChandrasekaranNullCone.boost_mismatch_D21
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-26T15:32:02.756045+00:00
-- url     : https://prove2.me/theorems/df6bebe4-9c93-4240-851f-a811e3c2a22c
-- title:
--   Boost invariance forces the subtracted-correlator relation, eq. (D.21)
-- statement:
--   Let $c_\perp,d,\eta\in\mathbb R$ with $d>0$, and let $G_{\sigma,0}(u,u')=-c_\perp/(u-u')^2$ be the vacuum two-point function (D.19). Let $G_\sigma:\mathbb R^2\to\mathbb R$ be any two-point function. Suppose that boosting the right insertion at fixed left insertion preserved $G_\sigma$:
--   $$G_\sigma(-d,d)=e^{\eta}\,G_\sigma(-d,e^{\eta}d).$$
--   Then the vacuum-subtracted correlators must satisfy
--   $$d^{2}\Big[(G_\sigma-G_{\sigma,0})(-d,d)-e^{\eta}(G_\sigma-G_{\sigma,0})(-d,e^{\eta}d)\Big]=\frac{c_\perp}{4}\tanh^{2}(\eta/2).$$
--
--   **Role in the source.** The subtracted correlators have finite coincidence limits at the corner, so the left-hand side vanishes as $d\to0$ at fixed $\eta\neq0$. The right-hand side is positive. The source uses this incompatibility to show that the relative boost cannot preserve $G_\sigma$.
--
--   **Formalization note.** $G_\sigma$ is an arbitrary function $\mathbb R\times\mathbb R\to\mathbb R$, written curried. The boost-invariance assumption is the hypothesis `hG`. The displayed equation is transcribed verbatim from (D.21), p. 71. No sign condition on $c_\perp$ and no restriction on $\eta$ is needed for the identity, so the statement is slightly more general than the source. The source has $c_\perp>0$, which makes the right-hand side strictly positive for $\eta\ne0$.
-- source:
--   Chandrasekaran 2026, An algebraic quantization of gravity from the null cone, https://arxiv.org/abs/2611.34924v1, Appendix D.2, p. 71, eq. (D.21): "If boosting l_R at fixed l_L preserved G_sigma, subtracting (D.19) would require d^2[(G_sigma - G_sigma,0)(-d,d) - e^eta (G_sigma - G_sigma,0)(-d, e^eta d)] = (c_perp/4) tanh^2(eta/2)"; vacuum two-point function eq. (D.19) / (5.28d).

import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ChandrasekaranNullCone

/-- Chandrasekaran (arXiv:2611.34924), eq. (D.21): if a two-point function `G` were invariant
under the relative boost, `G(-d,d) = e^η G(-d,e^η d)`, then subtracting the vacuum two-point
function `G₀(u,u') = -c/(u-u')²` (D.19) would require
`d²[(G-G₀)(-d,d) - e^η (G-G₀)(-d,e^η d)] = (c/4) tanh²(η/2)`. -/
theorem boost_mismatch_D21 (c d η : ℝ) (hd : 0 < d) (G : ℝ → ℝ → ℝ)
    (hG : G (-d) d = Real.exp η * G (-d) (Real.exp η * d)) :
    let G₀ : ℝ → ℝ → ℝ := fun u u' => -c / (u - u') ^ 2
    d ^ 2 * ((G (-d) d - G₀ (-d) d) - Real.exp η * (G (-d) (Real.exp η * d) - G₀ (-d) (Real.exp η * d)))
      = c / 4 * Real.tanh (η / 2) ^ 2 := by sorry

end ChandrasekaranNullCone
