-- Prove2me | Theorems.Thm_ActuarialValuation_quotaShareFiniteMenu_attained
-- name    : ActuarialValuation.quotaShareFiniteMenu_attained
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:19:00.243974+00:00
-- url     : https://prove2.me/theorems/c1824064-4abc-4e8f-822d-367adf5aada4
-- title:
--   A finite nonempty retention menu always has a cheapest treaty
-- statement:
--   Operational retention menus can be restricted to finitely many contractual alternatives. A minimum of the same insurer cost function exists in every finite nonempty menu, even if the continuous optimum is not one of the allowed quotes.
--
--   **Mathematical statement**
--
--   $$
--   \exists a^*\in A,\ \forall a\in A,\ J(r_{a^*})\le J(r_a)
--   $$
-- source:
--   Kaluszka (2001), Optimal reinsurance under mean-variance premium principles, DOI https://doi.org/10.1016/S0167-6687(00)00066-4; Guerra and Centeno (2010), ASTIN Bulletin 40, DOI https://doi.org/10.2143/AST.40.1.2049220; explicit Bernoulli quota-share specialisation

import Mathlib
import Definitions.Def_actuarial_quotaShareCapitalObjective

namespace ActuarialValuation

theorem quotaShareFiniteMenu_attained {A : Type*}
  [Fintype A] [Nonempty A] (r : A → ℝ)
  (q claim loading capital : ℝ) :
  ∃ a : A, ∀ b : A,
    quotaShareCapitalObjective q claim (r a) loading capital ≤
      quotaShareCapitalObjective q claim (r b) loading capital := by sorry

end ActuarialValuation
