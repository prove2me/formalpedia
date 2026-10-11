-- Prove2me | Theorems.Thm_ActuarialValuation_coInd_upper_ratio
-- name    : ActuarialValuation.coInd_upper_ratio
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:06:51.887982+00:00
-- url     : https://prove2.me/theorems/3c59e375-6041-4a62-a44c-297c0f829ef0
-- title:
--   Independent and dependent upper-tail co-exceedance: coInd_upper_ratio
-- statement:
--   Independence makes high-tail conditional exceedance probability decline with the tail threshold. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_coInd
import Definitions.Def_actuarial_coUpperRatio

namespace ActuarialValuation

theorem coInd_upper_ratio (u : ℝ) (hu : u≠1) : coUpperRatio coInd u=1-u := by sorry

end ActuarialValuation
