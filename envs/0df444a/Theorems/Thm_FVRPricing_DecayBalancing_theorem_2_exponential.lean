-- Prove2me | Theorems.Thm_FVRPricing_DecayBalancing_theorem_2_exponential
-- name    : FVRPricing.DecayBalancing.theorem_2_exponential
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:48:19.251089+00:00
-- url     : https://prove2.me/theorems/a2294042-4698-4b5a-9920-107bd7ccbc68
-- title:
--   Theorem 2 (exponential case) — $1/(1+\log\kappa(a))\le J^{\pi_{\rm db}}(z)/J^*(z)\le1$
-- statement:
--   Let reservation prices be exponential with mean $r>0$, $\alpha>0$ and $a,b>0$. For every state $z=(x,a,b)$, $J^*(z)$ is finite and
--   $$\frac1{1+\log\kappa(a)}\ \le\ \frac{J^{\pi_{\rm db}}(z)}{J^*(z)}\ \le\ 1 .$$
--
--   The bound does not depend on $x$, $b$, $\alpha$ or $r$, only on the coefficient of variation $1/\sqrt a$ of the prior.
--
--   **Formalization Note** Stated as $J^*(z)<\infty$, $J^{\pi_{\rm db}}(z)\le J^*(z)$ and $J^*(z)\le(1+\log\kappa(a))J^{\pi_{\rm db}}(z)$; with $J^*$ finite this is the ratio statement, and it holds trivially at $x=0$ where both values vanish. Only the exponential half is stated (the logit half uses an undefined distribution family and the rounded constant $1.27$).
-- source:
--   Farias, Van Roy, Dynamic Pricing with a Prior on Market Response, manuscript of January 20, 2009 (sha256 a64048ac…), p. 22, Theorem 2 (exponential half)

import Mathlib
import Definitions.Def_FVRPricing_DecayBalancing_Policies
import Definitions.Def_FVRPricing_DecayBalancing_Kappa

namespace FVRPricing.DecayBalancing

open MeasureTheory ProbabilityTheory

theorem theorem_2_exponential (r α : ℝ) (hr : 0 < r) (hα : 0 < α)
    (x : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Jstar (expDensity r) α x a b ≠ ⊤ ∧
    Jpi (expDensity r) α (πdb (expDensity r) α) x a b ≤ Jstar (expDensity r) α x a b ∧
    Jstar (expDensity r) α x a b ≤
      ENNReal.ofReal (1 + Real.log (kappa a)) * Jpi (expDensity r) α (πdb (expDensity r) α) x a b := by sorry

end FVRPricing.DecayBalancing
