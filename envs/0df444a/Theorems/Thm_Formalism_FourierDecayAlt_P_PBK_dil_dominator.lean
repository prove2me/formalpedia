-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_dil_dominator
-- name    : Formalism.FourierDecayAlt.P.PBK.dil_dominator
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:22:32.590796+00:00
-- url     : https://prove2.me/theorems/480f6f85-8c27-45f2-b6c9-a89106af4011
-- title:
--   PBK: dil dominator
-- statement:
--   The PBK construction uses the dil dominator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AestronglyMeasurableMainD.lean#L135-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AestronglyMeasurableMainD.lean#L135-L145

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoSmulCocompact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AestronglyMeasurableMainD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical

theorem Formalism.FourierDecayAlt.P.PBK.dil_dominator {α : Type} {l : Filter α} (ab : ℂ → ℝ) (hab : MemLp ab 2 volume) (lam : α → ℂ)
    (hlam : Tendsto lam l (𝓝 1)) :
    (∀ a D, ‖lam a‖ * ab (lam a * D) ≤ ab D + |‖lam a‖ * ab (lam a * D) - ab D|) ∧
    (∀ᶠ a in l, MemLp (fun D => |‖lam a‖ * ab (lam a * D) - ab D|) 2 volume) ∧
    Tendsto (fun a => ∫ D, |‖lam a‖ * ab (lam a * D) - ab D| ^ 2) l (𝓝 0) := by sorry
