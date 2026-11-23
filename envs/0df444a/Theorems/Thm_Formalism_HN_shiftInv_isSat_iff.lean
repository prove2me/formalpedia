-- Prove2me | Theorems.Thm_Formalism_HN_shiftInv_isSat_iff
-- name    : Formalism.HN.shiftInv_isSat_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:27:46.237789+00:00
-- url     : https://prove2.me/theorems/791e148d-3262-40b1-a364-138c0f35f5cd
-- title:
--   HN: shift Inv is Sat iff
-- statement:
--   The HN construction uses the shift Inv is Sat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/ShiftInvariance.lean#L19-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/ShiftInvariance.lean#L19-L39

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
universe u v w w₂

theorem Formalism.HN.shiftInv_isSat_iff {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E)
    {L : Submodule R V} (hL : IsLat ρ L) (N : Submodule R V) :
    IsSat ρ L N ↔
      N ≤ L ∧ ∀ N' : Submodule R V, N ≤ N' → N' ≤ L → rk ρ N' = rk ρ N → N' = N := by sorry
