-- Prove2me | Theorems.Thm_Deduction_eq_ofReal_sub_of_dist_le_of_le_sub_re
-- name    : Deduction.eq_ofReal_sub_of_dist_le_of_le_sub_re
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:35:05.494791+00:00
-- url     : https://prove2.me/theorems/5ddbfa2d-2c24-4301-b33c-31a649f6beb2
-- title:
--   Deduction: eq of Real sub of dist le of le sub re
-- statement:
--   The Deduction construction uses the eq of Real sub of dist le of le sub re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/LandauDichotomy.lean#L10-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/LandauDichotomy.lean#L10-L22

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LandauFinite
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LandauDichotomy
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

theorem Deduction.eq_ofReal_sub_of_dist_le_of_le_sub_re {w : ℂ} {σ D : ℝ} (h1 : dist w (σ : ℂ) ≤ D) (h2 : D ≤ σ - w.re) :
    w = ((σ - D : ℝ) : ℂ) := by sorry
