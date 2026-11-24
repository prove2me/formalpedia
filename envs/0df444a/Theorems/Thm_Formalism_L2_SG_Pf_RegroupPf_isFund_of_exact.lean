-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RegroupPf_isFund_of_exact
-- name    : Formalism.L2.SG.Pf.RegroupPf.isFund_of_exact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:32.186111+00:00
-- url     : https://prove2.me/theorems/46611df2-6ca6-4458-a2c6-ea1f893eb2ae
-- title:
--   Regroup Pf: is Fund of exact
-- statement:
--   The Regroup Pf construction uses the is Fund of exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RegroupPfUnfold.lean#L27-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RegroupPfUnfold.lean#L27-L37

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RegroupPfUnfold
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RegroupPf
variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H]

theorem Formalism.L2.SG.Pf.RegroupPf.isFund_of_exact (μ : Measure H) (R : Subgroup H) (W : Set H) (hm : MeasurableSet W)
    (hc : ∀ x, ∃ g ∈ R, g * x ∈ W) (hu : ∀ x ∈ W, ∀ g ∈ R, g * x ∈ W → g = 1) :
    IsFundamentalDomain R W μ := by sorry
