-- Prove2me | Theorems.Thm_FVRPricing_DecayBalancing_decay_balancing_one_third_normalized
-- name    : FVRPricing.DecayBalancing.decay_balancing_one_third_normalized
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-04T22:51:31.880192+00:00
-- url     : https://prove2.me/theorems/3e5a1417-5207-4512-9d2e-c8f455138d3f
-- title:
--   Theorem 3 in the normalization $r=1$, $\alpha=e^{-1}$: decay balancing earns at least one third of $J^*$
-- statement:
--   Theorem 3 of Farias–Van Roy in the normalization used in its proof: mean reservation price $r=1$ (so $\bar F(p)=e^{-p}$) and discount rate $\alpha=e^{-1}$.
--
--   Let the vendor start with $x>1$ units and a $\mathrm{Gamma}(a,b)$ prior on the arrival rate, $a>0$, $b>0$, and let $\pi_{\rm db}$ be the decay balancing policy defined with $\alpha=e^{-1}$, $r=1$:
--   $$\frac{\bar F(\pi_{\rm db}(z))}{\rho(\pi_{\rm db}(z))}\,\mu(z)=\alpha\tilde J(z),\qquad \mu(z)=a/b .$$
--   Then the optimal value is finite and
--   $$J^*(x,a,b)\ \le\ 3\,J^{\pi_{\rm db}}(x,a,b).$$
--
--   By the discount invariance (Lemma 5) and scale invariance (Lemma 10) of the model, this special case implies the general statement for every $\alpha>0$, $r>0$ (the reduction is proved on the platform for the mission's goal theorem).
-- source:
--   Farias, Van Roy, Dynamic Pricing with a Prior on Market Response, manuscript of January 20, 2009, p. 24, Theorem 3 and its proof (normalization alpha = e^{-1}, r = 1 justified by Lemmas 5 and 10); published in Operations Research 58(1):16-29, 2010

import Mathlib
import Definitions.Def_FVRPricing_DecayBalancing_Policies

namespace FVRPricing.DecayBalancing

open MeasureTheory ProbabilityTheory

theorem decay_balancing_one_third_normalized (x : ℕ) (hx : 1 < x) (a b : ℝ) (ha : 0 < a)
    (hb : 0 < b) :
    Jstar (expDensity 1) (Real.exp (-1)) x a b ≠ ⊤ ∧
    Jstar (expDensity 1) (Real.exp (-1)) x a b ≤
      3 * Jpi (expDensity 1) (Real.exp (-1)) (πdb (expDensity 1) (Real.exp (-1))) x a b := by sorry

end FVRPricing.DecayBalancing
