-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_generalised_put_time_dependent_pde
-- name    : FinancialDerivatives.FD06.generalised_put_time_dependent_pde
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:43:33.205278+00:00
-- url     : https://prove2.me/theorems/b78ff1f7-877e-4361-9546-4ef1a3469e86
-- title:
--   Variable-rate dividend-adjusted put Black-Scholes PDE
-- statement:
--   Variable-rate dividend-adjusted put Black-Scholes PDE
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6, with explicit analytic extensions.

import Mathlib
import Definitions.Def_fd06_bsSpatialOperator
import Definitions.Def_fd06_generalisedPut
import Definitions.Def_fd06_integratedRate
import Definitions.Def_fd06_integratedVariance
import Definitions.Def_fd06_integratedYield

namespace FinancialDerivatives.FD06

theorem generalised_put_time_dependent_pde (r q σ : ℝ → ℝ) (hr : Continuous r) (hq : Continuous q) (hσ : Continuous σ) (T t S K : ℝ) (hS : 0 < S) (hK : 0 < K) (ht : t < T) (hV : 0 < integratedVariance σ t T) : deriv (fun u => generalisedPut S K (integratedRate r u T) (integratedYield q u T) (integratedVariance σ u T)) t + bsSpatialOperator S (r t) (q t) (σ t) (generalisedPut S K (integratedRate r t T) (integratedYield q t T) (integratedVariance σ t T)) (deriv (fun s => generalisedPut s K (integratedRate r t T) (integratedYield q t T) (integratedVariance σ t T)) S) (deriv (deriv (fun s => generalisedPut s K (integratedRate r t T) (integratedYield q t T) (integratedVariance σ t T))) S) = 0 := by sorry

end FinancialDerivatives.FD06
