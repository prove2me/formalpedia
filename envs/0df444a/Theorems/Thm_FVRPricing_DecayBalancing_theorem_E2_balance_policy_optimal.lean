-- Prove2me | Theorems.Thm_FVRPricing_DecayBalancing_theorem_E2_balance_policy_optimal
-- name    : FVRPricing.DecayBalancing.theorem_E2_balance_policy_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:48:07.125051+00:00
-- url     : https://prove2.me/theorems/321adb1c-1d0e-4440-95f9-6bd6893f1266
-- title:
--   Lemma E.6(2) — the greedy (balance-price) policy $\pi^*$ is optimal
-- statement:
--   Let reservation prices be exponential with mean $r>0$, $\alpha>0$, and $a,b>0$. The policy $\pi^*$ that in every state $z$ posts the price solving the balance equation
--   $$\frac{\bar F(\pi^*(z))}{\rho(\pi^*(z))}\,\mu(z) = \alpha J^*(z)$$
--   is optimal: for every state $z = (x,a,b)$,
--   $$J^{\pi^*}(z) = J^*(z).$$
--
--   This is Lemma E.6(2) (the greedy policy with respect to the HJB solution, which equals $J^*$ by Lemma E.6(1) and exists by Appendix E, is optimal), i.e. the "if" direction of Theorem E.2 ("a policy $\pi$ is optimal if and only if $H^\pi J^* = 0$") applied to the greedy policy; p. 13 shows that the greedy price is the solution of the balance equation above. It justifies reading $\pi^*$ in Corollary 1, Lemma 9 and Theorem 3 as the optimal price.
--
--   **Formalization Note** The generator $H^\pi$ (which involves derivatives in $b$) is not formalized; the item states Lemma E.6(2), "the greedy/balance-price policy is optimal", and not the if-and-only-if characterization of Theorem E.2 over all policies. Appendix E restricts to exponential reservation prices and a Gamma prior, as here.
-- source:
--   Farias, Van Roy, Dynamic Pricing with a Prior on Market Response, manuscript of January 20, 2009 (sha256 a64048ac…), p. 47, Lemma E.6 (2) (with Theorem E.2, p. 42, and the existence of the HJB solution, Appendix E); p. 13 (balance characterization of π*)

import Mathlib
import Definitions.Def_FVRPricing_DecayBalancing_Policies

namespace FVRPricing.DecayBalancing

open MeasureTheory ProbabilityTheory

theorem theorem_E2_balance_policy_optimal (r α : ℝ) (hr : 0 < r) (hα : 0 < α)
    (x : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Jpi (expDensity r) α (πstar (expDensity r) α) x a b = Jstar (expDensity r) α x a b := by sorry

end FVRPricing.DecayBalancing
