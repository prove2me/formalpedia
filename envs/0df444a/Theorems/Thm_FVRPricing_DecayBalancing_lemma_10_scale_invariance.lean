-- Prove2me | Theorems.Thm_FVRPricing_DecayBalancing_lemma_10_scale_invariance
-- name    : FVRPricing.DecayBalancing.lemma_10_scale_invariance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:56.517486+00:00
-- url     : https://prove2.me/theorems/83c5603d-731b-423c-a172-ac2ec886eaed
-- title:
--   Lemma 10 — exponential reservation prices: invariance under rescaling the mean $r$
-- statement:
--   Let reservation prices be exponential with mean $r>0$, let $\pi$ be a policy and $\pi'(z) = \pi(z)/r$. Write $J^{\pi,\alpha,r}$ for the value of $\pi$ at discount rate $\alpha$ and mean reservation price $r$. Then for every state $z=(x,a,b)$ with $a,b>0$ and every $\alpha>0$,
--   $$J^{\pi,\alpha,r}(z) = r\,J^{\pi',\alpha,1}(z),\qquad\text{and in particular}\qquad J^{*,\alpha,r}(z) = r\,J^{*,\alpha,1}(z).$$
--
--   This licenses the normalization $r = 1$ in §6.3.
-- source:
--   Farias, Van Roy, Dynamic Pricing with a Prior on Market Response, manuscript of January 20, 2009 (sha256 a64048ac…), p. 23, Lemma 10

import Mathlib
import Definitions.Def_FVRPricing_DecayBalancing_Policies

namespace FVRPricing.DecayBalancing

open MeasureTheory ProbabilityTheory

theorem lemma_10_scale_invariance (π : ℕ → ℝ → ℝ → ℝ) (hπ : IsPolicy π)
    (α r : ℝ) (hα : 0 < α) (hr : 0 < r) (x : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Jpi (expDensity r) α π x a b =
      ENNReal.ofReal r * Jpi (expDensity 1) α (fun x a b => (1 / r) * π x a b) x a b ∧
    Jstar (expDensity r) α x a b = ENNReal.ofReal r * Jstar (expDensity 1) α x a b := by sorry

end FVRPricing.DecayBalancing
