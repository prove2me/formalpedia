-- Prove2me | Theorems.Thm_ActuarialValuation_ruinNextSurplus_zero_claim
-- name    : ActuarialValuation.ruinNextSurplus_zero_claim
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:28:11.660738+00:00
-- url     : https://prove2.me/theorems/046e8892-eada-4609-8899-44aece547c3b
-- title:
--   With no claim, a period adds the premium to surplus
-- statement:
--   If the insurance portfolio generates no claim payment during a period, only the fixed premium c affects the insurer's capital. The signed next-period surplus is therefore the old surplus plus the earned premium.
--
--   **Mathematical statement**
--
--   $$
--   U'=U+c
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 432 (Library PDF page 458), parent framework: Theorem 23.4 (Lundberg ruin bound). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.ruinNextSurplus_zero_claim is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinNextSurplus

namespace ActuarialValuation

theorem ruinNextSurplus_zero_claim (u : ℤ) (c : ℕ) :
  ruinNextSurplus u c 0 = u + (c : ℤ) := by sorry

end ActuarialValuation
