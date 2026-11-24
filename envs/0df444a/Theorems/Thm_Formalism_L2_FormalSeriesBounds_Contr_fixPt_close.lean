-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Contr_fixPt_close
-- name    : Formalism.L2.FormalSeriesBounds.Contr.fixPt_close
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:13.950584+00:00
-- url     : https://prove2.me/theorems/7188a06f-4f91-4e7b-b2e7-f137bddc5ca1
-- title:
--   Contr: fix Pt close
-- statement:
--   The Contr construction uses the fix Pt close property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffIterateZero.lean#L65-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffIterateZero.lean#L65-L67

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_fixPt_close

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {k : Type*} [Field k] {Z B : Type*}
open Formalism.L2.FormalSeriesBounds.Contr
variable {Ψ : (B → MvPowerSeries Z k) → (B → MvPowerSeries Z k)} (H : Contr Ψ)
include H

theorem Formalism.L2.FormalSeriesBounds.Contr.fixPt_close (n : ℕ) (c : B) : OrdGE (n + 1) (H.fixPt c - Ψ^[n] 0 c) := by sorry
