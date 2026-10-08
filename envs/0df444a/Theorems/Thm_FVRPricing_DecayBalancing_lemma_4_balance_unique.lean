-- Prove2me | Theorems.Thm_FVRPricing_DecayBalancing_lemma_4_balance_unique
-- name    : FVRPricing.DecayBalancing.lemma_4_balance_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:58.65169+00:00
-- url     : https://prove2.me/theorems/a24f9aa5-aa66-4afc-abd3-94faf261e6ca
-- title:
--   Lemma 4 — the decay balance equation has a unique solution, and it lies above $p^*$
-- statement:
--   Let $f$ satisfy Assumption 1, $\alpha>0$ satisfy Assumption 2, $a,b>0$, $\mu(z) = a/b$, and let the inventory be $x\ge1$. Then there is a unique $p\ge0$ with
--   $$\frac{\bar F(p)}{\rho(p)}\,\mu(z) = \alpha\tilde J(z),$$
--   and this solution is at least every static revenue-maximizing price $p^*$.
--
--   Lemma 4 makes the decay balancing price $\pi_{\rm db}$ of eq. (5) well defined; the location $p\ge p^*$ (stated in its proof, p. 35, as "the unique solution ... must be in $[p^*,\pi^*(z)]$") is used in Theorem 3 as $\pi_{\rm db}\ge 1$ when $r = 1$.
--
--   **Formalization Note** As printed ("for all $z\in\mathcal S$") the lemma is false at $x = 0$: then $\tilde J(z)=0$ while $\bar F(p)/\rho(p)>0$ for every finite $p$. The hypothesis $x\ge1$ is added for that reason. The single-Gamma case of the mixture statement is stated. $\tilde J$ is converted to a real number; Lemma 3 shows it is finite.
-- source:
--   Farias, Van Roy, Dynamic Pricing with a Prior on Market Response, manuscript of January 20, 2009 (sha256 a64048ac…), p. 13, Lemma 4; proof of Lemma 4, p. 35 (location of the solution in [p*, π*(z)])

import Mathlib
import Definitions.Def_FVRPricing_DecayBalancing_Policies

namespace FVRPricing.DecayBalancing

open MeasureTheory ProbabilityTheory

theorem lemma_4_balance_unique (f : ℝ → ℝ) (α : ℝ) (hα : 0 < α)
    (h1 : Assumption1 f) (h2 : Assumption2 f α) (x : ℕ) (hx : 1 ≤ x) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∃! p : ℝ, 0 ≤ p ∧ Fbar f p / hazard f p * (a / b) = α * (Jtilde f α x a b).toReal) ∧
    ∀ p q : ℝ, 0 ≤ p → Fbar f p / hazard f p * (a / b) = α * (Jtilde f α x a b).toReal →
      IsStaticMaximizer f q → q ≤ p := by sorry

end FVRPricing.DecayBalancing
