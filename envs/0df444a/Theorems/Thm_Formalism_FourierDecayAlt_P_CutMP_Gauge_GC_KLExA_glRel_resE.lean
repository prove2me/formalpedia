-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_KLExA_glRel_resE
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA.glRel_resE
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:15:01.174453+00:00
-- url     : https://prove2.me/theorems/9d428fb1-968d-45bb-899b-802c0a2400a5
-- title:
--   KLEx A: gl Rel res E
-- statement:
--   The KLEx A construction uses the gl Rel res E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreKLExistsOfAlg.lean#L55-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreKLExistsOfAlg.lean#L55-L64

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
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA.glRel_resE {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (S : Submodule ℂ V) (hS : Stab E S) :
    GlRel (resE E S hS) := by sorry
