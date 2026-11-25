-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_sum_rootSet_mul
-- name    : Formalism.FourierDecayAlt.P.PBK.sum_rootSet_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:34:28.752789+00:00
-- url     : https://prove2.me/theorems/c4096c13-ce02-4e67-b421-3906e680c58b
-- title:
--   PBK: sum root Set mul
-- statement:
--   The PBK construction uses the sum root Set mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormOfMemRootSetOne.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormOfMemRootSetOne.lean#L51-L55

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

theorem Formalism.FourierDecayAlt.P.PBK.sum_rootSet_mul {E : Type} [AddCommMonoid E] {s : ℕ} (hs : s ≠ 0) {w z ρ l : ℂ} (hw : w ≠ 0)
    (hz : z ^ s = w) (hρ : ρ ^ s = l) (hl : l ≠ 0) (Gf : ℂ → E) :
    ∑ y ∈ G.rootSet s (l * w), Gf y = ∑ ζ ∈ G.rootSet s 1, Gf (ζ * ρ * z) := by sorry
