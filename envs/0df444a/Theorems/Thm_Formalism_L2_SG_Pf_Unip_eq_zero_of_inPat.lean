-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_Unip_eq_zero_of_inPat
-- name    : Formalism.L2.SG.Pf.Unip.eq_zero_of_inPat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:12:34.062674+00:00
-- url     : https://prove2.me/theorems/ad9293dc-ff44-43c2-bae6-e29123128d63
-- title:
--   Unip: eq zero of in Pat
-- statement:
--   The Unip construction uses the eq zero of in Pat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L70-L73

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Unip
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K]
variable {lv : ι → ℕ} {k l : ℕ} {Z W : Matrix ι ι K}

theorem Formalism.L2.SG.Pf.Unip.eq_zero_of_inPat {L : ℕ} (hL : ∀ i, lv i < L) (hZ : InPat lv L Z) : Z = 0 := by sorry
