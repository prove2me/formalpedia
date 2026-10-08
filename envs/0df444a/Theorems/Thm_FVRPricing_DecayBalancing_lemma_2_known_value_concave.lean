-- Prove2me | Theorems.Thm_FVRPricing_DecayBalancing_lemma_2_known_value_concave
-- name    : FVRPricing.DecayBalancing.lemma_2_known_value_concave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:58.656358+00:00
-- url     : https://prove2.me/theorems/b412f36a-6828-4d11-9e3f-4a14ee0a2970
-- title:
--   Lemma 2 — $J^*_\lambda(x)$ is increasing and concave in $\lambda$
-- statement:
--   Let the reservation-price density $f$ satisfy Assumption 1 and let $\alpha>0$ be a discount rate for which Assumption 2 holds. For every inventory level $x\in\mathbb N$, the known-rate optimal value $\lambda\mapsto J^*_\lambda(x)$ is non-decreasing and concave on $\mathbb R_+ = [0,\infty)$, and for $x\ge1$ it is strictly increasing there:
--   $$\lambda\mapsto J^*_\lambda(x)\ \text{is increasing and concave on } \mathbb R_+ .$$
--
--   This is the decreasing-returns property in the arrival rate; by Jensen's inequality it yields $\tilde J(z)\le J^*_{\mu(z)}(x)$ in Lemma 3.
--
--   **Formalization Note** At $x=0$ the value is identically $0$, so "increasing" is stated strictly for $x\ge1$ and as monotone for all $x$. Assumption 2 includes finiteness, so the values are read as real numbers.
-- source:
--   Farias, Van Roy, Dynamic Pricing with a Prior on Market Response, manuscript of January 20, 2009 (sha256 a64048ac…), p. 9, Lemma 2 (with Assumptions 1 and 2)

import Mathlib
import Definitions.Def_FVRPricing_DecayBalancing_Policies

namespace FVRPricing.DecayBalancing

open MeasureTheory ProbabilityTheory

theorem lemma_2_known_value_concave (f : ℝ → ℝ) (α : ℝ) (hα : 0 < α)
    (h1 : Assumption1 f) (h2 : Assumption2 f α) (x : ℕ) :
    MonotoneOn (fun lam => (JstarKnown f α lam x).toReal) (Set.Ici 0) ∧
    (1 ≤ x → StrictMonoOn (fun lam => (JstarKnown f α lam x).toReal) (Set.Ici 0)) ∧
    ConcaveOn ℝ (Set.Ici 0) (fun lam => (JstarKnown f α lam x).toReal) := by sorry

end FVRPricing.DecayBalancing
