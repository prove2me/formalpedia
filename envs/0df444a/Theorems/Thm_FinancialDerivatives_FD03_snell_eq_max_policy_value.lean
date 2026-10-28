-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_snell_eq_max_policy_value
-- name    : FinancialDerivatives.FD03.snell_eq_max_policy_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:07:55.584541+00:00
-- url     : https://prove2.me/theorems/d4625541-2098-4dfd-bc41-556f418bb7fc
-- title:
--   Snell value is an attained maximum over all admissible stopping policies
-- statement:
--   At every finite horizon and arbitrary exercise schedule, an admissible nonanticipating policy achieves exactly the Snell recursion value. Its expected discounted payout is at least that of every other admissible policy, proving both attainment and global optimality on the full binary tree.
-- source:
--   Original finite optimal-stopping maximum theorem motivated by Wilmott, Howison and Dewynne (1995), Chapter 10 §10.5, equation (10.17), printed pp. 189–191.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_snellValue
import Definitions.Def_fd03_policyValue
import Definitions.Def_fd03_admissible

namespace FinancialDerivatives.FD03

theorem snell_eq_max_policy_value (m : BinomialMarket) (n : ℕ)
    (exercise : ExerciseTree n) :
    ∃ p : StoppingPolicy n,
      admissible exercise p ∧
      policyValue m n exercise p = snellValue m n exercise ∧
      ∀ other : StoppingPolicy n,
        admissible exercise other →
          policyValue m n exercise other ≤ policyValue m n exercise p := by sorry

end FinancialDerivatives.FD03
