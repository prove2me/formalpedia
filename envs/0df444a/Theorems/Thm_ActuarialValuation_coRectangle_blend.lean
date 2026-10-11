-- Prove2me | Theorems.Thm_ActuarialValuation_coRectangle_blend
-- name    : ActuarialValuation.coRectangle_blend
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:03:43.926783+00:00
-- url     : https://prove2.me/theorems/55c4495c-55f3-4bf0-8433-c59c50ec8609
-- title:
--   Rectangle probability, Fréchet bounds and copula construction: coRectangle_blend
-- statement:
--   Convex mixing preserves the rectangle-mass calculation. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_coBlend
import Definitions.Def_actuarial_coRectangle

namespace ActuarialValuation

theorem coRectangle_blend (alpha : ℝ) (C D : ℝ → ℝ → ℝ) (u1 u2 v1 v2 : ℝ) : coRectangle (coBlend alpha C D) u1 u2 v1 v2=alpha*coRectangle C u1 u2 v1 v2+(1-alpha)*coRectangle D u1 u2 v1 v2 := by sorry

end ActuarialValuation
