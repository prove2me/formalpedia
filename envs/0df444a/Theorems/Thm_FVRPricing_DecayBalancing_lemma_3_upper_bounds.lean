-- Prove2me | Theorems.Thm_FVRPricing_DecayBalancing_lemma_3_upper_bounds
-- name    : FVRPricing.DecayBalancing.lemma_3_upper_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:59.132658+00:00
-- url     : https://prove2.me/theorems/42e9442d-21bd-492f-8b4e-16b4fbf0b5ce
-- title:
--   Lemma 3 — $J^* \le \tilde J \le J^*_{\mu(z)}(x) \le \bar F(p^*)p^*\mu(z)/\alpha$
-- statement:
--   Let $f$ satisfy Assumption 1, let $\alpha>0$ satisfy Assumption 2, and consider a $\mathrm{Gamma}(a,b)$ prior with $a,b>0$, mean $\mu(z) = a/b$. For every state $z=(x,a,b)$,
--   $$J^*(z)\le\tilde J(z)\le J^*_{\mu(z)}(x)\le\frac{\bar F(p^*)p^*\mu(z)}{\alpha},$$
--   where $\bar F(p^*)p^* = \sup_{p\ge0}p\bar F(p)$ is the static revenue at the static revenue-maximizing price $p^*$.
--
--   The first inequality says that knowledge of $\lambda$ can only help; the second is Jensen's inequality with the concavity of Lemma 2; the third compares with selling at the static optimum forever. In particular all three values are finite.
--
--   **Formalization Note** The paper states Lemma 3 for Gamma mixtures; this item states the single-Gamma case on which §6 works. The last bound is written with $\sup_{p\ge0}p\bar F(p)$, which equals $\bar F(p^*)p^*$.
-- source:
--   Farias, Van Roy, Dynamic Pricing with a Prior on Market Response, manuscript of January 20, 2009 (sha256 a64048ac…), p. 12, Lemma 3

import Mathlib
import Definitions.Def_FVRPricing_DecayBalancing_Policies

namespace FVRPricing.DecayBalancing

open MeasureTheory ProbabilityTheory

theorem lemma_3_upper_bounds (f : ℝ → ℝ) (α : ℝ) (hα : 0 < α)
    (h1 : Assumption1 f) (h2 : Assumption2 f α) (x : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Jstar f α x a b ≤ Jtilde f α x a b ∧
    Jtilde f α x a b ≤ JstarKnown f α (a / b) x ∧
    JstarKnown f α (a / b) x ≤ staticRevenue f * ENNReal.ofReal (a / b) / ENNReal.ofReal α := by sorry

end FVRPricing.DecayBalancing
