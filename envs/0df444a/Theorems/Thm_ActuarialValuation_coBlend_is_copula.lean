-- Prove2me | Theorems.Thm_ActuarialValuation_coBlend_is_copula
-- name    : ActuarialValuation.coBlend_is_copula
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:05:02.686979+00:00
-- url     : https://prove2.me/theorems/110bc0ed-ed71-4611-8ba1-784fb8e77091
-- title:
--   Rectangle probability, Fréchet bounds and copula construction: coBlend_is_copula
-- statement:
--   Convex combinations of genuine copulas remain genuine copulas. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_coIsCopula

namespace ActuarialValuation

theorem coBlend_is_copula (alpha : ℝ) (ha : 0≤alpha) (hb : alpha≤1) (C D : ℝ → ℝ → ℝ) (hC : coIsCopula C) (hD : coIsCopula D) : coIsCopula (coBlend alpha C D) := by sorry

end ActuarialValuation
