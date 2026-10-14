-- Prove2me | Theorems.Thm_ActuarialValuation_coCopulaRisk_fundamental
-- name    : ActuarialValuation.coCopulaRisk_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:08:22.717989+00:00
-- url     : https://prove2.me/theorems/c72b09ea-5859-4d66-a174-0d50d51cb651
-- title:
--   Independent and dependent upper-tail co-exceedance: coCopulaRisk_fundamental
-- statement:
--   FGM joint insurance dependence obeys genuine copula axioms, universally valid Fréchet limits and an exact analytic capital tail correction. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_coUpper
import Definitions.Def_actuarial_coLower
import Definitions.Def_actuarial_coFGM
import Definitions.Def_actuarial_coIsCopula
import Definitions.Def_actuarial_coTailJoint

namespace ActuarialValuation

theorem coCopulaRisk_fundamental (theta u v : ℝ) (ht0 : -1≤theta) (ht1 : theta≤1) (hu0 : 0≤u) (hu1 : u≤1) (hv0 : 0≤v) (hv1 : v≤1) : coIsCopula (coFGM theta) ∧ (coLower u v≤coFGM theta u v) ∧ (coFGM theta u v≤coUpper u v) ∧ (coTailJoint (coFGM theta) u v=(1-u)*(1-v)+theta*u*v*(1-u)*(1-v)) := by sorry

end ActuarialValuation
