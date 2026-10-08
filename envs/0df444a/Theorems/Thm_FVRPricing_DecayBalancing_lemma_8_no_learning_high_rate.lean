-- Prove2me | Theorems.Thm_FVRPricing_DecayBalancing_lemma_8_no_learning_high_rate
-- name    : FVRPricing.DecayBalancing.lemma_8_no_learning_high_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:48:08.258755+00:00
-- url     : https://prove2.me/theorems/18378b4b-b65a-4dc1-85d8-a4a8f5841a47
-- title:
--   Lemma 8 — the no-learning policy at a higher true rate: $J^{\pi^{nl}}_\lambda(x)\ge J^*_\mu(x)$
-- statement:
--   Let $f$ satisfy Assumption 1, $\alpha>0$ satisfy Assumption 2, $\mu>0$ and $\lambda\ge\mu$. With $\pi^{nl} = \pi^*_\mu$ the optimal policy for the known rate $\mu$ (eq. (6)), for all $x\in\mathbb N$
--   $$J^{\pi^{nl}}_\lambda(x)\ \ge\ J^*_\mu(x).$$
--
--   Selling with the policy designed for a lower rate at a higher true rate earns at least the value designed for.
-- source:
--   Farias, Van Roy, Dynamic Pricing with a Prior on Market Response, manuscript of January 20, 2009 (sha256 a64048ac…), p. 20, Lemma 8

import Mathlib
import Definitions.Def_FVRPricing_DecayBalancing_Policies

namespace FVRPricing.DecayBalancing

open MeasureTheory ProbabilityTheory

theorem lemma_8_no_learning_high_rate (f : ℝ → ℝ) (α : ℝ) (hα : 0 < α)
    (h1 : Assumption1 f) (h2 : Assumption2 f α) (lam μ : ℝ) (hμ : 0 < μ) (hle : μ ≤ lam) (x : ℕ) :
    JstarKnown f α μ x ≤ JpiKnown f α lam (knownOptPrice f α μ) x := by sorry

end FVRPricing.DecayBalancing
