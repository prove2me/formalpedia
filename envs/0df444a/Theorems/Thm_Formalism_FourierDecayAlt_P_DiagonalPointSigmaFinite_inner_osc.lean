-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_inner_osc
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.inner_osc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:18:31.882065+00:00
-- url     : https://prove2.me/theorems/7d4a4bab-6960-41e3-8bb2-8300d7dcafe5
-- title:
--   Diagonal Point Sigma Finite: inner osc
-- statement:
--   The Diagonal Point Sigma Finite construction uses the inner osc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L129-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L129-L152

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable [CompleteSpace V]

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.inner_osc (hOm : OmConverges) (hCut : CutPhiBound) (hIn : InnerXY) {m : ℕ} {β : ℂ} {Kc : Set ℂ}
    (h0 : (0 : ℂ) ∉ Kc) {Φ : Mat (m + 1 + 1) → V} {A K ε : ℝ} {k : ℕ}
    (hA : ((m : ℝ) + 1) * ((m : ℝ) + 4) < A) (hε : 0 ≤ ε)
    (hΦ : DerivBound k (detSet (m + 1) Kc) (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ)
    {t c : ℂ} (ht : t ≠ 0) (ht1 : ‖t‖ ≤ 1) (hD : c * t ^ (m + 1) ∈ Kc) :
    Integrable (blockIntegrand β (m + 1) (cutPhi (‖t‖ ^ (-ε)) Φ) t c) (muBlock β (m + 1)) ∧
    Integrable (blockIntegrand β (m + 1) (cutPhiC (‖t‖ ^ (-ε)) Φ) t c) (muBlock β (m + 1)) ∧
    Integrable (oscIn β m ε Φ (c * t ^ (m + 1)) t) (muXY β m) ∧
      ((‖t‖ ^ ((m + 1) * (m + 2)) : ℝ) : ℂ) • OmBlock β (m + 1) (cutPhi (‖t‖ ^ (-ε)) Φ) t c =
        ∫ p : XY m, oscIn β m ε Φ (c * t ^ (m + 1)) t p ∂(muXY β m) := by sorry
