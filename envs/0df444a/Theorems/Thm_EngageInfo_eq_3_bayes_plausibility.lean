-- Prove2me | Theorems.Thm_EngageInfo_eq_3_bayes_plausibility
-- name    : EngageInfo.eq_3_bayes_plausibility
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:17:45.712991+00:00
-- url     : https://prove2.me/theorems/79d6939c-9d6f-439e-9ac4-d296eadc562e
-- title:
--   (2)–(3) — posteriors $0\le\alpha_l\le\alpha^0\le\alpha_h\le1$, Bayes plausibility, and the inversion (3)
-- statement:
--   Let the prior be $\alpha^0\in(0,1)$.
--
--   1. For every feasible design $\pi$: $0\le\alpha_l\le\alpha^0\le\alpha_h\le1$; $\Pr(h),\Pr(l)\in[0,1]$ with $\Pr(h)+\Pr(l)=1$; and the posteriors average to the prior,
--   $$\Pr(h)\,\alpha_h+\Pr(l)\,\alpha_l=\alpha^0 .$$
--   2. For $0\le a<\alpha^0<b\le1$, the design (3)
--   $$\pi_h=\frac{b(\alpha^0-a)}{\alpha^0(b-a)},\qquad \pi_l=\frac{(b-\alpha^0)(1-a)}{(1-\alpha^0)(b-a)}$$
--   is feasible, induces the posteriors $(\alpha_l,\alpha_h)=(a,b)$, and sends $h$ with probability $(\alpha^0-a)/(b-a)$.
--
--   Together these reduce the choice of a signal to the choice of a pair of posteriors around the prior, as in Kamenica and Gentzkow (2011).
--
--   Differences from the source:
--   - encoding: signals (π_h, π_l) with π_h ≥ 1 − π_l; posteriors by Bayes' rule → pairs (π_h, π_l) ∈ [0,1]² with π_h + π_l ≥ 1; the posterior after a probability-zero signal is set to the prior α⁰; reason: Bayes' rule leaves a null signal's posterior undefined; it has weight 0 in every expectation, so no value changes
--   - encoding: (3) for αl ∈ [0, α⁰], αh ∈ [α⁰, 1] → (3) for 0 ≤ a < α⁰ < b ≤ 1; reason: (3) divides by αh − αl, and if one posterior equals α⁰ the other signal has probability 0, so the posterior pair is not realized; the strict range is where (3) defines a design inducing the pair
-- source:
--   Guo, Designing Information to Engage Customers, Management Science (2025), doi:10.1287/mnsc.2022.03503, (2) and posteriors, p.6; (3), p.7

import Mathlib
import Definitions.Def_EngageInfo_designs

namespace EngageInfo

/-- **Posteriors of a binary signal, Bayes plausibility, and the inversion (3).**
Guo, *Designing Information to Engage Customers*, Management Science (2025), §2, pp.6–7: "let
αh ∈ [α⁰, 1] and αl ∈ [0, α⁰] be the updated probabilities for the state H, conditional on the
realized signal h or l, respectively. As in Kamenica and Gentzkow (2011), the information design
problem on π amounts to determining the posterior beliefs, under the constraint (due to the Bayes'
rule) that the expectation of the posteriors is equal to the prior"; (3), p.7.

Let `α⁰ ∈ (0, 1)`.
1. For every feasible design `π`: `0 ≤ α_l ≤ α⁰ ≤ α_h ≤ 1`, `Pr(h), Pr(l) ∈ [0, 1]`,
   `Pr(h) + Pr(l) = 1`, and `Pr(h)·α_h + Pr(l)·α_l = α⁰`.
2. For `0 ≤ a < α⁰ < b ≤ 1`, the design (3) with `α_l = a`, `α_h = b` is feasible, induces the
   posteriors `(a, b)`, and gives `Pr(h) = (α⁰ − a)/(b − a)`.

**Formalization Note** The posterior after a probability-zero signal is the prior (see `postH`,
`postL`). -/
theorem eq_3_bayes_plausibility (a0 : ℝ) (ha0 : a0 ∈ Set.Ioo (0 : ℝ) 1) :
    (∀ π ∈ designs,
      0 ≤ postL a0 π ∧ postL a0 π ≤ a0 ∧ a0 ≤ postH a0 π ∧ postH a0 π ≤ 1 ∧
      probH a0 π ∈ Set.Icc (0 : ℝ) 1 ∧ probL a0 π ∈ Set.Icc (0 : ℝ) 1 ∧
      probH a0 π + probL a0 π = 1 ∧
      probH a0 π * postH a0 π + probL a0 π * postL a0 π = a0) ∧
    (∀ a b : ℝ, 0 ≤ a → a < a0 → a0 < b → b ≤ 1 →
      designOf a0 a b ∈ designs ∧ Induces a0 (designOf a0 a b) a b ∧
      probH a0 (designOf a0 a b) = (a0 - a) / (b - a)) := by sorry

end EngageInfo
