-- Prove2me | Theorems.Thm_Deduction_iteratedDeriv_laplace_meas
-- name    : Deduction.iteratedDeriv_laplace_meas
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:34:47.385158+00:00
-- url     : https://prove2.me/theorems/1358b592-0d91-44ae-be05-0ca2b5ad7233
-- title:
--   Deduction: iterated Deriv laplace meas
-- statement:
--   The Deduction construction uses the iterated Deriv laplace meas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/IteratedDerivLaplace.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/IteratedDerivLaplace.lean#L16-L20

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_IteratedDerivLaplace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction

theorem Deduction.iteratedDeriv_laplace_meas (g : ℝ → ℝ) (hg : Measurable g) (k : ℕ) (z : ℂ) :
    AEStronglyMeasurable (fun u : ℝ => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-z * u))
      (volume.restrict (Ioi (0 : ℝ))) := by sorry
