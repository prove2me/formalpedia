-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_RadTTaylor_perm_of_swaps
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor.perm_of_swaps
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:15:03.168499+00:00
-- url     : https://prove2.me/theorems/822bd44e-c94a-45f3-8db4-c7123d5ca29e
-- title:
--   Rad TTaylor: perm of swaps
-- statement:
--   The Rad TTaylor construction uses the perm of swaps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCLRadTTaylor.lean#L11-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCLRadTTaylor.lean#L11-L24

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTTaylor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTTaylor.perm_of_swaps {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) W)
    (h : ∀ (a b : Fin n), a ≠ b → ∀ v : Fin n → E, T (v ∘ Equiv.swap a b) = T v) :
    ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E), T (v ∘ σ) = T v := by sorry
