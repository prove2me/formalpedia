-- Prove2me | Theorems.Thm_BalkemaDeHaan_LimitTypes_closing_display
-- name    : BalkemaDeHaan.LimitTypes.closing_display
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:20:42.935869+00:00
-- url     : https://prove2.me/theorems/ebaff426-7301-4f2a-bcdb-9c362ef201f1
-- title:
--   Proof of Theorem 1, closing display — each limit law G = 1 − S satisfies min(1, S(B(t) + xA(t))/S(t)) = S(x) for t > 0
-- statement:
--   For each of the four limit laws $G = \Pi$, $\Pi_\gamma$ ($\gamma > 0$), $\Gamma_\alpha$ ($\alpha > 0$) and $\Gamma_{\gamma,\alpha}$ ($\gamma, \alpha > 0$), write $S = 1 - G$. Then for every $t > 0$ there are $A(t) > 0$ and $B(t)$ such that
--   $$\min\Big(1, \frac{S(B(t) + xA(t))}{S(t)}\Big) = S(x) \qquad \text{for all } x \in \mathbb R.$$
--
--   Comparing with (3), this says that if $X$ has tail $S$ itself, then its normed residual life at every age $t > 0$ has exactly the law $G$; so each of the four types does occur as a limit, and Theorem 1 lists exactly the possible limit laws.
--
--   **Formalization Note** The four families are those of the introduction, each defined as $0$ for $x < 0$, so $S = 1$ there. The scale $A(t)$ is required to be positive, as a scale transformation is.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 797 (PDF 6), proof of Theorem 1, closing display

import Mathlib
import Definitions.Def_BalkemaDeHaan_LimitTypes_ResidualLife
import Definitions.Def_BalkemaDeHaan_LimitTypes_LimitLaws

open MeasureTheory ProbabilityTheory Filter Topology

namespace BalkemaDeHaan.LimitTypes

/-- Proof of Theorem 1, closing display, p. 797 (PDF 6): each limit law `G = 1 - S` of the four
families satisfies `min(1, S(B(t) + x A(t)) / S(t)) = S(x)` for every `t > 0`, with some
`A(t) > 0` and `B(t)`. -/
theorem closing_display :
    (∀ t : ℝ, 0 < t → ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, ∀ x : ℝ,
      min 1 ((1 - PiLaw (B + x * A)) / (1 - PiLaw t)) = 1 - PiLaw x) ∧
    (∀ γ : ℝ, 0 < γ → ∀ t : ℝ, 0 < t → ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, ∀ x : ℝ,
      min 1 ((1 - PiDiscreteLaw γ (B + x * A)) / (1 - PiDiscreteLaw γ t)) =
        1 - PiDiscreteLaw γ x) ∧
    (∀ α : ℝ, 0 < α → ∀ t : ℝ, 0 < t → ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, ∀ x : ℝ,
      min 1 ((1 - GammaLaw α (B + x * A)) / (1 - GammaLaw α t)) = 1 - GammaLaw α x) ∧
    (∀ γ : ℝ, 0 < γ → ∀ α : ℝ, 0 < α → ∀ t : ℝ, 0 < t → ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, ∀ x : ℝ,
      min 1 ((1 - GammaDiscreteLaw γ α (B + x * A)) / (1 - GammaDiscreteLaw γ α t)) =
        1 - GammaDiscreteLaw γ α x) := by sorry

end BalkemaDeHaan.LimitTypes
