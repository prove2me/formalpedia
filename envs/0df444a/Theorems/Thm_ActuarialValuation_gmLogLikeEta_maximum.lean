-- Prove2me | Theorems.Thm_ActuarialValuation_gmLogLikeEta_maximum
-- name    : ActuarialValuation.gmLogLikeEta_maximum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:08:45.955336+00:00
-- url     : https://prove2.me/theorems/75e71231-8133-454e-9230-d3b3341d8aac
-- title:
--   Poisson log-likelihood, score and information: gmLogLikeEta_maximum
-- statement:
--   Poisson log-likelihood attains a global maximum at the fitted canonical count for strictly positive observations. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   \ell(\eta)=y\log(Ee^\eta)-Ee^\eta,\quad U(\eta)=y-Ee^\eta
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 373. J. A. Nelder and R. W. M. Wedderburn (1972), Generalized Linear Models, JRSS A 135:370–384, https://doi.org/10.2307/2344614; actuarial practice in casualty generalized linear models https://www.casact.org/sites/default/files/2021-03/05-Goldburd-Khare-Tevet.pdf. Parent topic: Positive insurance exposure offsets, Poisson log-link likelihood and score, Fisher information, deviance and multiplicative premium relativities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.2307/2344614

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmMean
import Definitions.Def_actuarial_gmLogLikeEta

namespace ActuarialValuation

theorem gmLogLikeEta_maximum (claims exposure fitted candidate : ℝ) (hc : 0<claims) (he : 0<exposure) (hfit : gmMean exposure fitted=claims) : gmLogLikeEta claims exposure candidate≤gmLogLikeEta claims exposure fitted := by sorry

end ActuarialValuation
