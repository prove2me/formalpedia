-- Prove2me | Theorems.Thm_FVRPricing_DecayBalancing_lemma_7_no_learning_low_rate
-- name    : FVRPricing.DecayBalancing.lemma_7_no_learning_low_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:48:05.53313+00:00
-- url     : https://prove2.me/theorems/679e3822-41db-4a9f-9278-dc2f646f710a
-- title:
--   Lemma 7 — the no-learning policy at a lower true rate: $J^{\pi^{nl}}_\lambda(x)\ge(\lambda/\mu)J^*_\mu(x)$
-- statement:
--   Let $f$ satisfy Assumption 1, $\alpha>0$ satisfy Assumption 2, and let $0\le\lambda<\mu$. Let $\pi^{nl} = \pi^*_\mu$ be the optimal policy for the known arrival rate $\mu$ (eq. (6)). If the true arrival rate is $\lambda$, then for all $x\in\mathbb N$
--   $$J^{\pi^{nl}}_\lambda(x)\ \ge\ \frac{\lambda}{\mu}\,J^*_\mu(x).$$
--
--   Together with Lemma 8 this bounds the loss of a vendor who prices as if the arrival rate were known to equal its prior mean.
-- source:
--   Farias, Van Roy, Dynamic Pricing with a Prior on Market Response, manuscript of January 20, 2009 (sha256 a64048ac…), p. 20, Lemma 7

import Mathlib
import Definitions.Def_FVRPricing_DecayBalancing_Policies

namespace FVRPricing.DecayBalancing

open MeasureTheory ProbabilityTheory

theorem lemma_7_no_learning_low_rate (f : ℝ → ℝ) (α : ℝ) (hα : 0 < α)
    (h1 : Assumption1 f) (h2 : Assumption2 f α) (lam μ : ℝ) (hlam : 0 ≤ lam) (hμ : 0 < μ)
    (hlt : lam < μ) (x : ℕ) :
    ENNReal.ofReal (lam / μ) * JstarKnown f α μ x ≤ JpiKnown f α lam (knownOptPrice f α μ) x := by sorry

end FVRPricing.DecayBalancing
