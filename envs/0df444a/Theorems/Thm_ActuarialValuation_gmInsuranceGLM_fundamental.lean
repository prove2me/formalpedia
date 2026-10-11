-- Prove2me | Theorems.Thm_ActuarialValuation_gmInsuranceGLM_fundamental
-- name    : ActuarialValuation.gmInsuranceGLM_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:12:43.512657+00:00
-- url     : https://prove2.me/theorems/88af500e-01aa-4616-a707-a703a99fc2e8
-- title:
--   Claims deviance, premium relativity and model comparison: gmInsuranceGLM_fundamental
-- statement:
--   A genuine positive-exposure Poisson GLM has the correct canonical offset, score and Fisher derivative, nonnegative saturated deviance and consistent severity-loaded insurance premium. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   D_{\text{Poi}}=2\left[y\log\left(\frac{y}{\mu}\right)-(y-\mu)\right]
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 373. J. A. Nelder and R. W. M. Wedderburn (1972), Generalized Linear Models, JRSS A 135:370–384, https://doi.org/10.2307/2344614; actuarial practice in casualty generalized linear models https://www.casact.org/sites/default/files/2021-03/05-Goldburd-Khare-Tevet.pdf. Parent topic: Positive insurance exposure offsets, Poisson log-link likelihood and score, Fisher information, deviance and multiplicative premium relativities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.2307/2344614

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmMean
import Definitions.Def_actuarial_gmRate
import Definitions.Def_actuarial_gmLogMean
import Definitions.Def_actuarial_gmPurePremium
import Definitions.Def_actuarial_gmLogLikeEta
import Definitions.Def_actuarial_gmScore
import Definitions.Def_actuarial_gmInformation
import Definitions.Def_actuarial_gmPoissonDeviance
import Definitions.Def_actuarial_gmRatingPremium

namespace ActuarialValuation

theorem gmInsuranceGLM_fundamental (claims exposure eta severity : ℝ) (hc : 0<claims) (he : 0<exposure) (hs : 0≤severity) : (Real.log (gmMean exposure eta)=gmLogMean exposure eta) ∧ HasDerivAt (fun x => gmLogLikeEta claims exposure x) (gmScore claims exposure eta) eta ∧ HasDerivAt (fun x => gmScore claims exposure x) (-gmInformation exposure eta) eta ∧ (0≤gmPoissonDeviance claims (gmMean exposure eta)) ∧ (gmRatingPremium exposure eta severity=exposure*gmPurePremium (gmRate eta) severity) := by sorry

end ActuarialValuation
