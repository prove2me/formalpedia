-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_levelCeil_tower
-- name    : Formalism.EigenvalueLevelCeiling.levelCeil_tower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:52.078362+00:00
-- url     : https://prove2.me/theorems/d43af74a-8401-4c68-9756-fff5e97c0dcf
-- title:
--   Eigenvalue Level Ceiling: level Ceil tower
-- statement:
--   The Eigenvalue Level Ceiling construction uses the level Ceil tower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/GlobalBoundRefinements.lean#L512-L517
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/GlobalBoundRefinements.lean#L512-L517

import Definitions.Def_Formalism_MirabolicMackeyTheory_LocalConditionsWeighted
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues

theorem Formalism.EigenvalueLevelCeiling.levelCeil_tower (ρ1 ρ2 : ℤ) (T : ℕ) (DL Dk g : ℝ) (h1 : 0 ≤ ρ1) (h2 : 0 ≤ ρ2) (h3 : 0 ≤ DL)
    (h4 : (T : ℝ) * DL ≤ Dk) (h5 : 2 * Dk + 2 < g) :
    ρ1 * ⌈(ρ2 : ℝ) * ((T : ℝ) * (DL / (g - 1) + 1))⌉ ≤ (ρ1 * ρ2) * ((T : ℤ) + 1) := by sorry
