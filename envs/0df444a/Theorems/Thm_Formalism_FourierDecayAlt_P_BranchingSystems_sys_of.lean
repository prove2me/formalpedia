-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_sys_of
-- name    : Formalism.FourierDecayAlt.P.BranchingSystems.sys_of
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:51:07.033356+00:00
-- url     : https://prove2.me/theorems/6b6a926a-3ff8-4606-a00c-43266bf670de
-- title:
--   Branching Systems: sys of
-- statement:
--   The Branching Systems construction uses the sys of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BranchingSystems.lean#L206-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BranchingSystems.lean#L206-L246

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BranchingSystems
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BranchingSystems
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem Formalism.FourierDecayAlt.P.BranchingSystems.sys_of (hSM : ExistsSingMax) (hCS : CapSing) (hSR : SubRel) (hR : RaiseNZ) (hLo : LowerNZ)
    {n : ℕ} {E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V} {β : ℂ} {L : Fin (n + 1) → ℤ}
    (H : Hyp E β L) : Sys L (fun M => CapSp (subA E) (shf β M) ≠ ⊥) := by sorry
