-- Prove2me | Theorems.Thm_ActuarialValuation_coRectangle_zero_height
-- name    : ActuarialValuation.coRectangle_zero_height
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:02:53.398474+00:00
-- url     : https://prove2.me/theorems/0ef213d9-cec4-47b7-b58a-9cefd93aa1ee
-- title:
--   Rectangle probability, Fréchet bounds and copula construction: coRectangle_zero_height
-- statement:
--   A rectangle of zero height has zero joint probability mass. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_coRectangle

namespace ActuarialValuation

theorem coRectangle_zero_height (C : ℝ → ℝ → ℝ) (u1 u2 v : ℝ) : coRectangle C u1 u2 v v=0 := by sorry

end ActuarialValuation
