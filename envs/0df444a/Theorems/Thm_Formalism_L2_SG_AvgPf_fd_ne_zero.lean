-- Prove2me | Theorems.Thm_Formalism_L2_SG_AvgPf_fd_ne_zero
-- name    : Formalism.L2.SG.AvgPf.fd_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:23.029901+00:00
-- url     : https://prove2.me/theorems/655b3c98-424d-4356-8f79-4ad69ccd610b
-- title:
--   Avg Pf: fd ne zero
-- statement:
--   The Avg Pf construction uses the fd ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/LieAveraging/LsSetresAvg.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/LieAveraging/LsSetresAvg.lean#L27-L31

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_LieAveraging_LsSetresAvg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Set
open scoped Pointwise ENNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.AvgPf

theorem Formalism.L2.SG.AvgPf.fd_ne_zero {Γ α : Type*} [Group Γ] [MulAction Γ α] [MeasurableSpace α] {μ : Measure α}
    [MeasurableConstSMul Γ α] [SMulInvariantMeasure Γ α μ] [Countable Γ] {S : Set α}
    (h : IsFundamentalDomain Γ S μ) (hμ : μ univ ≠ 0) : μ S ≠ 0 := by sorry
