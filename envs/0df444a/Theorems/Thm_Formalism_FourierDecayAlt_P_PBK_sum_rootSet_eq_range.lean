-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_sum_rootSet_eq_range
-- name    : Formalism.FourierDecayAlt.P.PBK.sum_rootSet_eq_range
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:53:34.763848+00:00
-- url     : https://prove2.me/theorems/5c34398c-ba74-4b4f-83c8-c2200aec649f
-- title:
--   PBK: sum root Set eq range
-- statement:
--   The PBK construction uses the sum root Set eq range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormOfMemRootSetOne.lean#L57-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormOfMemRootSetOne.lean#L57-L63

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormOfMemRootSetOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open MeasureTheory Filter Topology Set Polynomial
noncomputable section
open Classical

theorem Formalism.FourierDecayAlt.P.PBK.sum_rootSet_eq_range {E : Type} [AddCommMonoid E] {s : ℕ} (hs : s ≠ 0) {w : ℂ} (hw : w ≠ 0)
    (F : ℂ → E) : ∑ z ∈ G.rootSet s w, F z = ∑ k ∈ Finset.range s, F (NthRootMeasurability.R s k w) := by sorry
