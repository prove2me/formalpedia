-- Prove2me | Theorems.Thm_ActuarialValuation_cm1RedingtonImmunisation_fundamental
-- name    : ActuarialValuation.cm1RedingtonImmunisation_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:40:16.523375+00:00
-- url     : https://prove2.me/theorems/394f2e79-0c82-4972-b960-1618556642a1
-- title:
--   Bond pricing and immunisation: cm1RedingtonImmunisation_fundamental
-- statement:
--   The genuine Redington second-derivative test gives a local surplus minimum at the matching effective yield; it does not assert global or arbitrary curve immunisation. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   S(i_0)=S'(i_0)=0,\ S''(i_0)>0 \Longrightarrow S(i)\ge0\text{ locally}
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 4. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1CashflowPV
import Definitions.Def_actuarial_cm1ProfitGap

namespace ActuarialValuation

theorem cm1RedingtonImmunisation_fundamental (assets liabilities : ℕ → ℝ) (n : ℕ) (i₀ : ℝ)
  (hi : -1 < i₀)
  (hPV : cm1ProfitGap assets liabilities n i₀ = 0)
  (hD : deriv (cm1ProfitGap assets liabilities n) i₀ = 0)
  (hC : 0 < deriv (deriv (cm1ProfitGap assets liabilities n)) i₀) :
  ∃ ε : ℝ, 0 < ε ∧ ∀ i : ℝ,
    |i-i₀| < ε → cm1CashflowPV liabilities n i ≤ cm1CashflowPV assets n i := by sorry

end ActuarialValuation
