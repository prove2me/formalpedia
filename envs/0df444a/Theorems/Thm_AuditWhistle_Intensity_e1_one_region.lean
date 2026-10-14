-- Prove2me | Theorems.Thm_AuditWhistle_Intensity_e1_one_region
-- name    : AuditWhistle.Intensity.e1_one_region
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:18:17.112435+00:00
-- url     : https://prove2.me/theorems/7993f6e8-eaec-4485-918b-5b5a304026c2
-- title:
--   Appendix, proof of Proposition 2, p. 33 — the region e₁* = 1: r > r₂ and a* < a₂, with r₂ < r* and a₁ < a₂
-- statement:
--   Fix a model and $\tau\in(0,1)$, write $r=R/\gamma$, and let $r_2=\frac{p+\beta-2p\beta}{(1-p)\beta}$, $a_2=\frac{\beta+\beta p(r-2)+p-\beta r}{\beta(p-1)(r-1)}$. Then:
--
--   1. for $a\in(0,1)$,
--   $$r\,\frac{(1-p)(1-a)\beta}{(1-p)(1-a)\beta+p(1-\beta)}>1\iff r>r_2\ \text{and}\ a<a_2;$$
--   2. $r_2<r^*(p,\beta,\tau)$;
--   3. if $r>r^*$, then every $a\in(0,1)$ at which $\partial V_1/\partial\tau(a)\ge0$ satisfies $a<a_2$, i.e. the threshold $a_1$ lies below $a_2$.
--
--   These facts confirm the conjecture $e_1^*=1$ in the region $r>r^*$, $d<d^*$.
--
--   **Formalization Note** The page prints "$\ge1\iff$" and "$r_2>r^*$". The first fails at $a=a_2$, where the left side equals $1$, so the strict form is stated. The second is reversed: $r_2<r^*$ holds for all admissible parameters (e.g. $p=\tfrac12$, $\beta=\tfrac9{10}$, $\tau=\tfrac12$ give $r_2\approx1.11$, $r^*\approx1.71$), and it is this direction that makes $r>r^*$ imply $r>r_2$. Item 3 states "$a_1<a_2$" without naming $a_1$.
-- source:
--   Nan, Tang & Ye, Auditing with a Chance of Whistleblowing, author manuscript dated December 30, 2024 (Management Science, DOI 10.1287/mnsc.2024.04808), p. 33, Appendix, proof of Proposition 2

import Mathlib
import Definitions.Def_AuditWhistle_Intensity_Setting
import Definitions.Def_AuditWhistle_Intensity_Reaction

namespace AuditWhistle.Intensity

theorem e1_one_region (M : Model) (τ : ℝ) (hτ : τ ∈ Set.Ioo (0:ℝ) 1) :
    (∀ a ∈ Set.Ioo (0:ℝ) 1,
      (1 < M.R / M.γ * ((1 - M.p) * (1 - a) * M.β /
          ((1 - M.p) * (1 - a) * M.β + M.p * (1 - M.β))) ↔
        r2 M.p M.β < M.R / M.γ ∧ a < a2 M.p M.β (M.R / M.γ))) ∧
    r2 M.p M.β < rStar M.p M.β τ ∧
    (rStar M.p M.β τ < M.R / M.γ → ∀ a ∈ Set.Ioo (0:ℝ) 1,
      0 ≤ deriv (fun t => V1 M t a) τ → a < a2 M.p M.β (M.R / M.γ)) := by sorry

end AuditWhistle.Intensity
