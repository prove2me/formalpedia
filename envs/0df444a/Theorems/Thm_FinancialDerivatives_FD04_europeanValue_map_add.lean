-- Prove2me | Theorems.Thm_FinancialDerivatives_FD04_europeanValue_map_add
-- name    : FinancialDerivatives.FD04.europeanValue_map_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:48:42.189013+00:00
-- url     : https://prove2.me/theorems/27ca93f5-bdef-4926-99df-c6c0357deb6e
-- title:
--   Additivity of finite-tree European valuation
-- statement:
--   Pricing the pointwise sum of two signed payoff functions equals summing their separate backward-induction prices.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_payoffTreeMap

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

theorem europeanValue_map_add (m : BinomialMarket) (n : ℕ)
    (tree : PayoffTree n) (f g : ℝ → ℝ) :
    europeanValue m n (payoffTreeMap (fun x => f x + g x) n tree) =
      europeanValue m n (payoffTreeMap f n tree) +
      europeanValue m n (payoffTreeMap g n tree) := by sorry

end FinancialDerivatives.FD04
