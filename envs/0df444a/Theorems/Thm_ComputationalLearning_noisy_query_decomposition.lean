-- Prove2me | Theorems.Thm_ComputationalLearning_noisy_query_decomposition
-- name    : ComputationalLearning.noisy_query_decomposition
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:24:25.278385+00:00
-- url     : https://prove2.me/theorems/d86c43e8-cf95-4b99-99bb-f8a5323d337b
-- title:
--   Equation (5.2): P_χ = p₁ (Pr_{EX_CN(c,D₁)}[χ = 1] − η)/(1 − 2η) + Pr_{EX_CN(c,D)}[χ = 1 ∧ x ∈ X₂], simulating a statistical query from noisy examples
-- statement:
--   **Equation (5.2)** (p. 113). Let $X_1$ be the set of inputs $x$ with $\chi(x, 0) \ne \chi(x, 1)$ and $X_2$ its complement; let $p_1 = \Pr_{x \sim D}[x \in X_1]$ and $D_1$ be $D$ restricted to $X_1$. Then
--   $$P_\chi = p_1\,\frac{\Pr_{EX^\eta_{CN}(c, D_1)}[\chi = 1] - \eta}{1 - 2\eta} + \Pr_{EX^\eta_{CN}(c, D)}[(\chi = 1) \wedge (x \in X_2)],$$
--   obtained from $P_\chi = p_1 \Pr_{EX(c, D_1)}[\chi = 1] + \Pr_{EX(c,D)}[(\chi = 1) \wedge (x \in X_2)]$ (5.1), the replacement of the correct label by a noisy one on $X_2$, and $\Pr_{EX_{CN}(c, D_1)}[\chi = 1] = \eta + (1 - 2\eta)\Pr_{EX(c, D_1)}[\chi = 1]$ on $X_1$. Every quantity on the right can be estimated from the noisy oracle, which is the key to simulating statistical query algorithms in the presence of classification noise (Theorem 5.3).
--
--   Formally: for a distribution $D$, measurable $c$ and $\chi$, and $0 \le \eta < 1/2$, the identity above with $D_1$ the conditional measure $D[\cdot \mid X_1]$ (the zero measure if $D(X_1) = 0$, in which case the first term vanishes) and the probabilities taken under the noisy example laws.
-- source:
--   Kearns and Vazirani, An Introduction to Computational Learning Theory, MIT Press 1994, doi:10.7551/mitpress/3897.001.0001, §5.4.1 pp. 112-113, the decomposition of P_χ, Equations (5.1)-(5.2), the key idea of Theorem 5.3

import Definitions.Def_ComputationalLearning_Noise

open MeasureTheory ProbabilityTheory

namespace ComputationalLearning

/-- **Equation (5.2)** (§5.4.1, p. 113), the decomposition of `P_χ` in terms of quantities
estimable from the noisy oracle. For a statistical query `χ`, let `X₁` be the inputs on which
the label matters, `p₁ = Pr_{x ~ D}[x ∈ X₁]`, and `D₁` the distribution `D` restricted to `X₁`.
Then
`P_χ = p₁ · (Pr_{EX_CN(c, D₁)}[χ = 1] − η)/(1 − 2η) + Pr_{EX_CN(c, D)}[(χ = 1) ∧ (x ∈ X₂)]`,
where the first probability is under the noisy oracle on `D₁` (Equation (5.1) and the identity
`Pr_{EX_CN(c,D₁)}[χ = 1] = η + (1 − 2η) Pr_{EX(c,D₁)}[χ = 1]`) and the second under the noisy
oracle on `D` (on `X₂` a noisy label can replace the correct one). Stated for `0 ≤ η < 1/2`,
measurable `c` and `χ`; if `p₁ = 0` the conditional is the zero measure and the first term
vanishes. -/
theorem noisy_query_decomposition {X : Type*} [MeasurableSpace X] (D : Measure X)
    [IsProbabilityMeasure D] (c : X → Bool) (hc : Measurable c) (χ : X × Bool → Bool)
    (hχ : Measurable χ) {η : ℝ} (hη0 : 0 ≤ η) (hη : η < 1 / 2) :
    queryProb D c χ =
      (D (labelSensitive χ)).toReal *
        ((noisyExampleLaw (D[|labelSensitive χ]) c η {p | χ p = true}).toReal - η) / (1 - 2 * η) +
      (noisyExampleLaw D c η {p | χ p = true ∧ p.1 ∉ labelSensitive χ}).toReal := by sorry

end ComputationalLearning
