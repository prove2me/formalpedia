-- Prove2me | Theorems.Thm_ActuarialValuation_coFGM_tail_spread_pos
-- name    : ActuarialValuation.coFGM_tail_spread_pos
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:07:26.719365+00:00
-- url     : https://prove2.me/theorems/a8b968f4-d877-4f6f-b187-bc8eb97469c8
-- title:
--   Independent and dependent upper-tail co-exceedance: coFGM_tail_spread_pos
-- statement:
--   Nonnegative FGM dependence increases joint high-loss risk over independence. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   \Pr(U>u,V>v)=1-u-v+C(u,v)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 4. Sklar (1959), Fonctions de répartition à n dimensions et leurs marges, Publications de l'Institut de Statistique de l'Université de Paris; actuarial copula dependence in risk, https://www.mdpi.com/1911-8074/12/2/65; dependent insurance exposures, https://doi.org/10.1007/s13385-022-00326-0. Parent topic: Bivariate copula margins, rectangle 2-increasing criterion, Fréchet-Hoeffding bounds, FGM mixtures and insurance tail co-exceedance. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.mdpi.com/1911-8074/12/2/65

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coFGM
import Definitions.Def_actuarial_coThresholdSpread

namespace ActuarialValuation

theorem coFGM_tail_spread_pos (theta u v : ℝ) (ht : 0≤theta) (hu0 : 0≤u) (hu1 : u≤1) (hv0 : 0≤v) (hv1 : v≤1) : 0≤coThresholdSpread (coFGM theta) u v := by sorry

end ActuarialValuation
