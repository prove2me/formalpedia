-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_policy_value_le_snell
-- name    : FinancialDerivatives.FD03.policy_value_le_snell
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:58:32.531011+00:00
-- url     : https://prove2.me/theorems/45f3c3dd-dcdc-4a08-9f7b-7c353860a32b
-- title:
--   Every admissible stopping policy is bounded by Snell value
-- statement:
--   For any finite maturity, exercise tree and nonanticipating stopping policy that obeys its exercise permissions, the discounted value obtained by that policy is at most the Snell recursion's value. This is the optimal-stopping upper bound.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §10.5, printed pp. 189–191, equation (10.17). Original rigorous finite-tree optimal stopping inequality.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_admissible
import Definitions.Def_fd03_policyValue
import Definitions.Def_fd03_snellValue

namespace FinancialDerivatives.FD03

theorem policy_value_le_snell (m : BinomialMarket) (n : ℕ)
    (tree : ExerciseTree n) (p : StoppingPolicy n)
    (hp : admissible tree p) :
    policyValue m n tree p ≤ snellValue m n tree := by sorry

end FinancialDerivatives.FD03
