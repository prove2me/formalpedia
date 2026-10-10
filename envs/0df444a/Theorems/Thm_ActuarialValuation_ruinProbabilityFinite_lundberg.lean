-- Prove2me | Theorems.Thm_ActuarialValuation_ruinProbabilityFinite_lundberg
-- name    : ActuarialValuation.ruinProbabilityFinite_lundberg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:32:03.38283+00:00
-- url     : https://prove2.me/theorems/0f488b4b-61fb-48be-ac6a-7e2766de7636
-- title:
--   Finite-horizon discrete ruin probability obeys an exponential adjustment bound
-- statement:
--   The proof inducts on the finite horizon. Already-ruined negative states are bounded because exp(−Ru)≥1 for R≥0. From a solvent state, previous-horizon ruin probabilities are dominated pointwise by next-state exponentials; the nonnegative weighted sum factors into exp(−Ru) times the adjustment moment, which is no greater than one.
--
--   **Mathematical statement**
--
--   $$
--   M(R)\le1,\ R\ge0\Longrightarrow\psi_n(u)\le e^{-Ru}
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 432 (Library PDF page 458), parent framework: Theorem 23.4 (Lundberg ruin bound). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.ruinProbabilityFinite_lundberg is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinProbabilityFinite
import Definitions.Def_actuarial_ruinAdjustmentMoment
import Definitions.Def_actuarial_ruinExponentialBound
import Definitions.Def_actuarial_ruinNextSurplus

namespace ActuarialValuation

theorem ruinProbabilityFinite_lundberg
  (w : ℕ → ℝ) (B c n : ℕ) (u : ℤ) (R : ℝ)
  (hw : ∀ k, 0 ≤ w k) (hR : 0 ≤ R)
  (hmoment : ruinAdjustmentMoment w B c R ≤ 1) :
  ruinProbabilityFinite w B c n u ≤ ruinExponentialBound R u := by sorry

end ActuarialValuation
