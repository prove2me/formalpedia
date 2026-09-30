-- Prove2me | Theorems.Thm_ComputationalLearning_noisy_disagreement
-- name    : ComputationalLearning.noisy_disagreement
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:24:06.434771+00:00
-- url     : https://prove2.me/theorems/e7c572dd-513b-4e50-9027-c1956c5bf446
-- title:
--   p. 117: the probability that h disagrees with the noisy label is γ_h = η + (1 − 2η) error(h)
-- statement:
--   **p. 117.** If we define $\gamma_h = \Pr_{EX^\eta_{CN}(c, D)}[h(x) \ne b]$ (the probability $h$ disagrees with the label provided by the noisy oracle), then $\gamma_h = (1-\eta)\,\mathrm{error}(h) + \eta(1 - \mathrm{error}(h)) = \eta + (1 - 2\eta)\,\mathrm{error}(h)$, and $\gamma_{h_i} - \gamma_{h_j} = (1 - 2\eta)(\mathrm{error}(h_i) - \mathrm{error}(h_j))$.
--
--   Formally: for a distribution $D$, measurable $c$ and $h$, and $0 \le \eta \le 1$, the probability under the noisy example law that $h(x) \ne b$ equals $\eta + (1 - 2\eta)\,\mathrm{error}_D(h)$.
-- source:
--   Kearns and Vazirani, An Introduction to Computational Learning Theory, MIT Press 1994, doi:10.7551/mitpress/3897.001.0001, §5.4.3 p. 117, the identity used to select the best hypothesis among the simulations

import Definitions.Def_ComputationalLearning_Noise

open MeasureTheory ProbabilityTheory

namespace ComputationalLearning

/-- **The disagreement probability under noise** (§5.4.3, p. 117). If `γ_h` is the probability that
`h` disagrees with the label provided by the noisy oracle, then
`γ_h = (1 − η) error(h) + η (1 − error(h)) = η + (1 − 2η) error(h)`; hence
`γ_{h_i} − γ_{h_j} = (1 − 2η)(error(h_i) − error(h_j))`, and the hypothesis with the smallest
estimated `γ` has the smallest error. -/
theorem noisy_disagreement {X : Type*} [MeasurableSpace X] (D : Measure X)
    [IsProbabilityMeasure D] (c h : X → Bool) (hc : Measurable c) (hh : Measurable h) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (noisyExampleLaw D c η {p | h p.1 ≠ p.2}).toReal = η + (1 - 2 * η) * errorOf D c h := by sorry

end ComputationalLearning
