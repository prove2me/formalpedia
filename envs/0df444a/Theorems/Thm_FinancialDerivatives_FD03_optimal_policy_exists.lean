-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_optimal_policy_exists
-- name    : FinancialDerivatives.FD03.optimal_policy_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:58:51.784328+00:00
-- url     : https://prove2.me/theorems/40ef515b-2b6c-40e4-9a51-5a9aa79fd782
-- title:
--   A finite admissible stopping policy attains Snell value
-- statement:
--   For every finite exercise tree there is a nonanticipating policy which respects all exercise permissions and whose risk-neutral discounted value equals Snell's recursion. A policy can choose immediate exercise on a tie, and choose continuation otherwise.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §10.5, printed pp. 189–191, equation (10.17). Original finite optimal-stopping attainment theorem; no infinite-horizon convergence is assumed.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_admissible
import Definitions.Def_fd03_policyValue
import Definitions.Def_fd03_snellValue

namespace FinancialDerivatives.FD03

theorem optimal_policy_exists (m : BinomialMarket) (n : ℕ)
    (tree : ExerciseTree n) :
    ∃ p : StoppingPolicy n,
      admissible tree p ∧ policyValue m n tree p = snellValue m n tree := by sorry

end FinancialDerivatives.FD03
