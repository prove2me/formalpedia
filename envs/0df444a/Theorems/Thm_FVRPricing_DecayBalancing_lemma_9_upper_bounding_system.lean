-- Prove2me | Theorems.Thm_FVRPricing_DecayBalancing_lemma_9_upper_bounding_system
-- name    : FVRPricing.DecayBalancing.lemma_9_upper_bounding_system
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:55.431988+00:00
-- url     : https://prove2.me/theorems/1f49f226-b343-45b2-a9c2-ca07944f6ecd
-- title:
--   Lemma 9 — the upper-bounding system: $J^{ub}(z)\ge J^*(z)$
-- statement:
--   Let $f$ satisfy Assumption 1, $\alpha>0$ satisfy Assumption 2, and $a,b>0$. Consider the system whose state evolves as under the decay balancing policy $\pi_{\rm db}$ but which is paid, at each sale, the optimal price $\pi^*$ of the pre-sale state:
--   $$R^{ub}(z) = \sum_{k:\,t_k\le\tau}e^{-\alpha t_k}\,\pi^*(z_{t_k-}),\qquad J^{ub}(z) = E_z[R^{ub}(z)].$$
--   Then for every state $z=(x,a,b)$,
--   $$J^{ub}(z)\ \ge\ J^*(z).$$
--
--   Combined with Corollary 1, which compares $R^{\rm db}$ and $R^{ub}$ sale by sale, this gives Theorem 2.
--
--   **Formalization Note** p. 21 writes the discount as $e^{-e^{-1}t_k}$, i.e. under the normalization $\alpha = e^{-1}$ of p. 18; the statement is given for a general $\alpha>0$, the form Lemma 5 makes equivalent.
-- source:
--   Farias, Van Roy, Dynamic Pricing with a Prior on Market Response, manuscript of January 20, 2009 (sha256 a64048ac…), p. 21, §6.2, definitions of R^db, R^ub, J^ub and Lemma 9

import Mathlib
import Definitions.Def_FVRPricing_DecayBalancing_Policies

namespace FVRPricing.DecayBalancing

open MeasureTheory ProbabilityTheory

theorem lemma_9_upper_bounding_system (f : ℝ → ℝ) (α : ℝ) (hα : 0 < α)
    (h1 : Assumption1 f) (h2 : Assumption2 f α) (x : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Jstar f α x a b ≤ Jub f α x a b := by sorry

end FVRPricing.DecayBalancing
