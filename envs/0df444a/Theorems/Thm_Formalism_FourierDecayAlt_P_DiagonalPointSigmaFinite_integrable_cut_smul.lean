-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_integrable_cut_smul
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.integrable_cut_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:18:23.017716+00:00
-- url     : https://prove2.me/theorems/3af1b562-dd4f-4e2e-94b4-f994a4eaf04a
-- title:
--   Diagonal Point Sigma Finite: integrable cut smul
-- statement:
--   The Diagonal Point Sigma Finite construction uses the integrable cut smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L84-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L84-L92

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

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.integrable_cut_smul {β : ℂ} {m : ℕ} {F : XY m → V} (hF : Integrable F (muXY β m))
    {χ : (Fin (m + 1) → ℂ) → ℝ} (hχ : Continuous χ) {B : ℝ} (hB : ∀ x, |χ x| ≤ B) :
    Integrable (fun p : XY m => ((χ p.1 : ℝ) : ℂ) • F p) (muXY β m) := by sorry
