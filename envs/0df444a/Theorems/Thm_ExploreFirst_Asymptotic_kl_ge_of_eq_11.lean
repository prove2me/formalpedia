-- Prove2me | Theorems.Thm_ExploreFirst_Asymptotic_kl_ge_of_eq_11
-- name    : ExploreFirst.Asymptotic.kl_ge_of_eq_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:24:48.239999+00:00
-- url     : https://prove2.me/theorems/d2ca5304-054c-45f3-a893-d07a720298cb
-- title:
--   Equation (11), p. 9 — entropy lower bound for Bernoulli KL
-- statement:
--   Let $p,q\in[0,1]$ and let $\mathrm{kl}(p,q)$ be Bernoulli relative entropy. The decomposition in equation (11) gives
--
--   $$
--   \mathrm{kl}(p,q)\ge\max\!\left\{0,\ (1-p)\ln\frac1{1-q}-\ln2\right\}.
--   $$
--
--   This is the entropy estimate used for the second inequality of equation (10).
--
--   **Formalization Note** Both sides are extended nonnegative reals. The Lean statement explicitly assigns $+\infty$ to the lower bound when $q=1$ and $p<1$, matching the Bernoulli KL boundary value.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 9, (11) and the second inequality of (10)

import Mathlib
import Definitions.Def_ExploreFirst_Asymptotic_Setting

namespace ExploreFirst.Asymptotic

theorem kl_ge_of_eq_11 (p q : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    (if q = 1 ∧ p < 1 then (⊤ : ENNReal)
      else ENNReal.ofReal ((1 - p) * Real.log (1 / (1 - q)) - Real.log 2)) ≤
      ExploreFirst.FundIneq.klBer p q := by sorry

end ExploreFirst.Asymptotic
