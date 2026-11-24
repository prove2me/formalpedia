-- Prove2me | Theorems.Thm_Formalism_L2_SG_GGMirabolic_ratio_numeric
-- name    : Formalism.L2.SG.GGMirabolic.ratio_numeric
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:18.38637+00:00
-- url     : https://prove2.me/theorems/d5c1e55f-19f7-4d47-bec9-5d6c8d471e75
-- title:
--   GGMirabolic: ratio numeric
-- statement:
--   The GGMirabolic construction uses the ratio numeric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GGMirabolic.lean#L91-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GGMirabolic.lean#L91-L96

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolicBase
import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.GGMirabolic
open Finset Matrix
open scoped ComplexConjugate ComplexOrder
noncomputable section
open Classical

theorem Formalism.L2.SG.GGMirabolic.ratio_numeric (k : ℕ) (q : ℝ) (hq : 3 ≤ q) :
    ∏ i ∈ Finset.Ico 1 k, (1 - (q ^ i)⁻¹)⁻¹ ≤ 1 + 3 / q := by sorry
