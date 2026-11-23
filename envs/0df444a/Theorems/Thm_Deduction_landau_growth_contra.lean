-- Prove2me | Theorems.Thm_Deduction_landau_growth_contra
-- name    : Deduction.landau_growth_contra
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:34:50.129506+00:00
-- url     : https://prove2.me/theorems/9819e4b3-1e82-4a07-87ed-84409886ecad
-- title:
--   Deduction: landau growth contra
-- statement:
--   The Deduction construction uses the landau growth contra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/LandauGrowthContra.lean#L9-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/LandauGrowthContra.lean#L9-L40

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LandauGrowthContra
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

theorem Deduction.landau_growth_contra {c d e C : ℝ} (hc : 0 < c) (hd : 0 < d) (hde : d < e) :
    ∃ η : ℝ, 0 < η ∧ ∃ U₀ : ℝ, ∀ U ≥ U₀, ∀ k : ℕ, U ≤ k → C * Real.exp (η * U) / e ^ k < c / d ^ k := by sorry
