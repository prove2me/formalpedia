-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_memLp_abar
-- name    : Formalism.FourierDecayAlt.P.PBK.memLp_abar
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:22:06.19892+00:00
-- url     : https://prove2.me/theorems/31b73f27-f606-4edd-a766-9efac8530e37
-- title:
--   PBK: mem Lp abar
-- statement:
--   The PBK construction uses the mem Lp abar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AestronglyMeasurableMainD.lean#L96-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AestronglyMeasurableMainD.lean#L96-L119

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
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem Formalism.FourierDecayAlt.P.PBK.memLp_abar {s : ℕ} (hs : s ≠ 0) {ε : ℂ} (hε : ‖ε‖ = 1) {bt : ℂ → H} (hbt : StronglyMeasurable bt)
    (hb : MemLp (bz s bt) 2 volume) :
    MemLp (abar s ε bt) 2 volume ∧ ∫ D, abar s ε bt D ^ 2 ≤ s * ∫ z, ‖bz s bt z‖ ^ 2 := by sorry
