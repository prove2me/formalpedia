-- Prove2me | Theorems.Thm_ActuarialValuation_coRectangle_add_v
-- name    : ActuarialValuation.coRectangle_add_v
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:03:15.524982+00:00
-- url     : https://prove2.me/theorems/58632ae4-40cf-4ed0-a9f5-b7c012045f88
-- title:
--   Rectangle probability, Fréchet bounds and copula construction: coRectangle_add_v
-- statement:
--   Adjacent vertical rectangles add their probability mass. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

theorem coRectangle_add_v (C : ℝ → ℝ → ℝ) (u1 u2 v1 v2 v3 : ℝ) : coRectangle C u1 u2 v1 v3=coRectangle C u1 u2 v1 v2+coRectangle C u1 u2 v2 v3 := by sorry

end ActuarialValuation
