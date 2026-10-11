-- Prove2me | Theorems.Thm_ActuarialValuation_coFGM_is_copula
-- name    : ActuarialValuation.coFGM_is_copula
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:04:50.247992+00:00
-- url     : https://prove2.me/theorems/0a1ea9b0-6cf2-4b88-83dd-1065a4f90f8d
-- title:
--   Rectangle probability, Fréchet bounds and copula construction: coFGM_is_copula
-- statement:
--   FGM is a genuine copula when its dependence parameter is in the unit interval around zero. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   \max(0,u+v-1)\le C(u,v)\le\min(u,v)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 4. Sklar (1959), Fonctions de répartition à n dimensions et leurs marges, Publications de l'Institut de Statistique de l'Université de Paris; actuarial copula dependence in risk, https://www.mdpi.com/1911-8074/12/2/65; dependent insurance exposures, https://doi.org/10.1007/s13385-022-00326-0. Parent topic: Bivariate copula margins, rectangle 2-increasing criterion, Fréchet-Hoeffding bounds, FGM mixtures and insurance tail co-exceedance. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.mdpi.com/1911-8074/12/2/65

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coFGM
import Definitions.Def_actuarial_coIsCopula

namespace ActuarialValuation

theorem coFGM_is_copula (theta : ℝ) (hl : -1≤theta) (hu : theta≤1) : coIsCopula (coFGM theta) := by sorry

end ActuarialValuation
