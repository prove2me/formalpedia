-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_finiteBinomial_pricing_and_optimal_exercise
-- name    : FinancialDerivatives.FD03.finiteBinomial_pricing_and_optimal_exercise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:09:18.542733+00:00
-- url     : https://prove2.me/theorems/d3eb2531-0425-46aa-aa2b-6fe6193bf60b
-- title:
--   Complete finite-binomial replication, arbitrage-free pricing and optimal exercise
-- statement:
--   For any strict finite binomial market and horizon, every signed European terminal claim has a self-financing replicator with a unique initial value given by backward induction, and this value is the only arbitrage-free derivative quotation. Every exercise schedule has an admissible nonanticipating stopping policy that attains the Snell value and dominates all other admissible policies; the same Snell value is attained by an adapted seller superhedge and is a lower bound for every seller superhedge. Finally, for any stock-dependent payoff, the efficient recombining-row algorithm agrees exactly with valuation on the full binary tree. All claims hold for arbitrary finite horizons, including maturity zero.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 10 §§10.2–10.5, equations (10.16) and (10.17), printed pp. 182–191. Original finite-market capstone combining the chapter's exact replication, unique no-arbitrage quote, Bermudan/American optimal exercise and recombining algorithm with explicit seller superhedging equivalence.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_SelfFinancing
import Definitions.Def_fd03_hedgeTerminalPays
import Definitions.Def_fd03_hedgeWealth
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_quotedClaimArbitrage
import Definitions.Def_fd03_admissible
import Definitions.Def_fd03_policyValue
import Definitions.Def_fd03_snellValue
import Definitions.Def_fd03_hedgeCoversExercise
import Definitions.Def_fd03_rowToRoot
import Definitions.Def_fd03_terminalRow
import Definitions.Def_fd03_payoffTreeMap
import Definitions.Def_fd03_terminalStockTree

namespace FinancialDerivatives.FD03

theorem finiteBinomial_pricing_and_optimal_exercise
    (m : BinomialMarket) (n : ℕ) (claim : PayoffTree n)
    (exercise : ExerciseTree n) (reward : ℝ → ℝ) :
    (∃ hedge : HedgeTree n,
      SelfFinancing m n m.initialSpot hedge ∧
      hedgeTerminalPays n hedge claim ∧
      hedgeWealth m n m.initialSpot hedge = europeanValue m n claim) ∧
    (∀ hedge : HedgeTree n,
      SelfFinancing m n m.initialSpot hedge →
      hedgeTerminalPays n hedge claim →
      hedgeWealth m n m.initialSpot hedge = europeanValue m n claim) ∧
    (∀ quote : ℝ,
      ¬ quotedClaimArbitrage m n m.initialSpot claim quote ↔
        quote = europeanValue m n claim) ∧
    (∃ p : StoppingPolicy n,
      admissible exercise p ∧
      policyValue m n exercise p = snellValue m n exercise ∧
      ∀ other : StoppingPolicy n,
        admissible exercise other →
          policyValue m n exercise other ≤ policyValue m n exercise p) ∧
    (∃ writer : HedgeTree n,
      SelfFinancing m n m.initialSpot writer ∧
      hedgeCoversExercise m n m.initialSpot writer exercise ∧
      hedgeWealth m n m.initialSpot writer = snellValue m n exercise) ∧
    (∀ writer : HedgeTree n,
      SelfFinancing m n m.initialSpot writer →
      hedgeCoversExercise m n m.initialSpot writer exercise →
      snellValue m n exercise ≤ hedgeWealth m n m.initialSpot writer) ∧
    rowToRoot m n (terminalRow m n reward) =
      europeanValue m n
        (payoffTreeMap reward n
          (terminalStockTree m n m.initialSpot)) := by sorry

end FinancialDerivatives.FD03
