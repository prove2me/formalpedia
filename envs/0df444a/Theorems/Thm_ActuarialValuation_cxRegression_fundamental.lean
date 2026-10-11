-- Prove2me | Theorems.Thm_ActuarialValuation_cxRegression_fundamental
-- name    : ActuarialValuation.cxRegression_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:20:32.734978+00:00
-- url     : https://prove2.me/theorems/09d328a4-e574-4317-90d1-1756ca9fb82f
-- title:
--   Log-partial likelihood, weighted risk scores and inference: cxRegression_fundamental
-- statement:
--   Cox covariates alter baseline hazard multiplicatively, survival stays within probability bounds, and the nontrivial risk-set score is derived as the derivative of the conditional partial likelihood. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   U(\beta)=\sum_{i\in D}\left(z_i-\frac{\sum_{j\in R_i}z_je^{\beta z_j}}{\sum_{j\in R_i}e^{\beta z_j}}\right)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 190. D. R. Cox (1972), Regression Models and Life-Tables, Journal of the Royal Statistical Society B 34:187–202, https://doi.org/10.1111/j.2517-6161.1972.tb00899.x; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, lifetime failure-time models. Parent topic: Multiplicative baseline hazard, finite at-risk sets, partial likelihood, censored selection, score derivatives and survival prediction. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.1111/j.2517-6161.1972.tb00899.x

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxSurvival
import Definitions.Def_actuarial_cxHazardRatio
import Definitions.Def_actuarial_cxLogPartial
import Definitions.Def_actuarial_cxScore

namespace ActuarialValuation

theorem cxRegression_fundamental {n : ℕ} (beta base H z1 z2 : ℝ) (events : Finset (Fin n)) (risks : Fin n → Finset (Fin n)) (z : Fin n → ℝ) (hb : base≠0) (hH : 0≤H) (hr : ∀ i∈events, (risks i).Nonempty) : (cxHazardRatio base beta z1 z2=Real.exp (beta*(z1-z2))) ∧ (cxSurvival H beta z1≤1) ∧ HasDerivAt (fun t => cxLogPartial t events risks z) (cxScore beta events risks z) beta := by sorry

end ActuarialValuation
