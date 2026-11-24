-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_KLExA_ofFn_prod_int
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA.ofFn_prod_int
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:47:46.706654+00:00
-- url     : https://prove2.me/theorems/48de1fea-bae8-4e0d-ba30-d331d3e8dd7c
-- title:
--   KLEx A: of Fn prod int
-- statement:
--   The KLEx A construction uses the of Fn prod int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreKLExistsOfAlg.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreKLExistsOfAlg.lean#L15-L21

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
variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA.ofFn_prod_int {t : ℕ} (F : Fin t → Module.End ℂ V) (F' : Fin t → Module.End ℂ V') (f : V →ₗ[ℂ] V')
    (h : ∀ k x, f (F k x) = F' k (f x)) (x : V) : f ((List.ofFn F).prod x) = (List.ofFn F').prod (f x) := by sorry
