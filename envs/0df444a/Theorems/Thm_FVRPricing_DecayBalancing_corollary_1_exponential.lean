-- Prove2me | Theorems.Thm_FVRPricing_DecayBalancing_corollary_1_exponential
-- name    : FVRPricing.DecayBalancing.corollary_1_exponential
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:48:29.936985+00:00
-- url     : https://prove2.me/theorems/40c7cee4-ff88-41cd-b905-19f7d0a0d61b
-- title:
--   Corollary 1 (exponential case) — $1/(1+\log\kappa(a))\le\pi_{\rm db}(z)/\pi^*(z)\le1$
-- statement:
--   Let reservation prices be exponential with mean $r>0$, $\alpha>0$, $a,b>0$, and inventory $x\ge1$. Then the decay balancing price and the optimal price at $z=(x,a,b)$ satisfy
--   $$\frac1{1+\log\kappa(a)}\ \le\ \frac{\pi_{\rm db}(z)}{\pi^*(z)}\ \le\ 1 .$$
--
--   Decay balancing prices are never above the optimal prices and never below them by more than the factor $1+\log\kappa(a)$.
--
--   **Formalization Note** Stated as $0<\pi_{\rm db}(z)$, $\pi_{\rm db}(z)\le\pi^*(z)$ and $\pi^*(z)\le(1+\log\kappa(a))\pi_{\rm db}(z)$, which is the ratio statement with the ratio well defined. $x\ge1$ is added because both prices are defined by balance equations that have no solution at $x=0$. Only the exponential half is stated: the "logit reservation price distributions" of the second half are never defined in the paper, have support $\mathbb R$ (contrary to Assumption 1), and come with the rounded constant $1.27$.
-- source:
--   Farias, Van Roy, Dynamic Pricing with a Prior on Market Response, manuscript of January 20, 2009 (sha256 a64048ac…), p. 20, Corollary 1 (exponential half)

import Mathlib
import Definitions.Def_FVRPricing_DecayBalancing_Policies
import Definitions.Def_FVRPricing_DecayBalancing_Kappa

namespace FVRPricing.DecayBalancing

open MeasureTheory ProbabilityTheory

theorem corollary_1_exponential (r α : ℝ) (hr : 0 < r) (hα : 0 < α)
    (x : ℕ) (hx : 1 ≤ x) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 < πdb (expDensity r) α x a b ∧
    πdb (expDensity r) α x a b ≤ πstar (expDensity r) α x a b ∧
    πstar (expDensity r) α x a b ≤ (1 + Real.log (kappa a)) * πdb (expDensity r) α x a b := by sorry

end FVRPricing.DecayBalancing
