-- Prove2me | Theorems.Thm_AmbDiversify_Smooth_smoothCE_raise_upper_le
-- name    : AmbDiversify.Smooth.smoothCE_raise_upper_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:08.205011+00:00
-- url     : https://prove2.me/theorems/8b94a4d1-e836-4026-8e55-c7cc8a9004c8
-- title:
--   Proof of Props 4.1–4.2, p. 16 (PDF 17) — the concavity step behind (A.8): raising the larger utility by d raises CE_φ by at most (1 − µ)d
-- statement:
--   Let $\phi$ be an ambiguity function of an ambiguity-averse decision maker ($C^2$, $\phi'>0$, concave), let $0\le\mu\le1$, let $x_1\le x_2$ and $d\ge0$. Then
--
--   $$\phi^{-1}\big(\mu\phi(x_1)+(1-\mu)\phi(x_2+d)\big)\;\le\;\phi^{-1}\big(\mu\phi(x_1)+(1-\mu)\phi(x_2)\big)+(1-\mu)\,d.$$
--
--   Raising the utility of the better-off expert by $d$ raises the smooth-model certainty equivalent by at most the ambiguity-neutral amount $(1-\mu)d$. It is the fact that the sentence "under the concavity of $\phi$, inequality (A.8) is satisfied if $\Delta(2)>\Delta(1)$" relies on in case (ii) of Proposition 4.1, where the expert with the higher no-diversification utility is also the one with the larger value of diversification.
--
--   **Formalization Note** This is a repaired reading, not (A.8) as printed: (A.6)–(A.8) take an expectation $\mathbb E_\Delta$ over a random $\tilde\Delta$ whose law the paper never specifies, so they cannot be stated as written. The statement above is the deterministic two-expert inequality that the cited sentence needs. $\phi^{-1}$ is `Function.invFun φ`.
-- source:
--   Berger & Eeckhoudt, Risk, ambiguity, and the value of diversification, iRisk Working Paper 2021-iRisk-02 (IÉSEG, April 2021), p. 16 (PDF 17), proof of Propositions 4.1 and 4.2, (A.8) and 'It is easy to show that, under the concavity of φ, inequality (A.8) is satisfied if ∆(2) > ∆(1)' (repaired reading)

import Mathlib
import Definitions.Def_AmbDiversify_Smooth_Model

namespace AmbDiversify.Smooth

/-- Proof of Propositions 4.1 and 4.2, p. 16, the concavity step behind (A.8) (repaired reading):
for an ambiguity-averse `φ`, raising the larger of the two expert utilities, `x2 ≥ x1`, by
`d ≥ 0` raises the certainty equivalent `φ⁻¹(µφ(x1) + (1 − µ)φ(x2))` by at most `(1 − µ)d`. -/
theorem smoothCE_raise_upper_le (φ : ℝ → ℝ) (hφ : IsAmbiguityFunction φ)
    (μ x1 x2 d : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hx : x1 ≤ x2) (hd : 0 ≤ d) :
    smoothCE φ μ x1 (x2 + d) ≤ smoothCE φ μ x1 x2 + (1 - μ) * d := by sorry

end AmbDiversify.Smooth
