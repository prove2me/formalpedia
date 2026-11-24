-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_KLExA_sum_projI
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA.sum_projI
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:49:10.175937+00:00
-- url     : https://prove2.me/theorems/dd6da8ee-18c4-480b-a0a4-21898ee15491
-- title:
--   KLEx A: sum proj I
-- statement:
--   The KLEx A construction uses the sum proj I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreKLExistsOfAlg.lean#L116-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreKLExistsOfAlg.lean#L116-L123

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreKLExistsOfAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Submodule ℂ V}

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA.sum_projI (h : DirectSum.IsInternal S) (v : V) : ∑ j, (projI h j v : V) = v := by sorry
