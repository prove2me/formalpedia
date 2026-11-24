-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_KLExA_resE_apply
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA.resE_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:48:12.816263+00:00
-- url     : https://prove2.me/theorems/6cca7e0e-e026-4015-85bb-6cb3dfe6bab5
-- title:
--   KLEx A: res E apply
-- statement:
--   The KLEx A construction uses the res E apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreKLExistsOfAlg.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreKLExistsOfAlg.lean#L52-L53

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

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA.resE_apply (E : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V) (hS : Stab E S) (a b : Fin n) (x : S) :
    ((resE E S hS a b x : S) : V) = E a b x := by sorry
