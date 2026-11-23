-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_gr_term
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.gr_term
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:56.467902+00:00
-- url     : https://prove2.me/theorems/22234b41-4f15-4435-a76f-96f09d5e1515
-- title:
--   Diagonal Point Sigma Finite: gr term
-- statement:
--   The Diagonal Point Sigma Finite construction uses the gr term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L624-L667
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L624-L667

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

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.gr_term (m : ℕ) (Cz Yz Lz OLz : V) (ψ : ℂ) (hψ : ‖ψ‖ = 1) (τ ζ a3 a4 : ℝ) (hτ : 0 < τ) (hζ : 0 < ζ)
    (h3 : ‖Cz - (ψ * ((τ ^ (m + 1) * ζ ^ (m + 1) / ((m : ℝ) + 2) : ℝ) : ℂ)) • Yz‖ ≤ a3 * τ ^ (m + 2))
    (h4 : ‖Yz - (((ζ ^ (2 * (m + 1)))⁻¹ : ℝ) : ℂ) • Lz‖ ≤ a4 * τ)
    (hL : Lz = ((ζ ^ ((m + 1 + 1) * (m + 1)) : ℝ) : ℂ) • OLz) :
    ‖(((τ ^ (m + 1))⁻¹ : ℝ) : ℂ) • Cz -
        ((m : ℂ) + 2)⁻¹ • ((((ζ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * 1 * ψ) • OLz)‖ ≤ (a3 + ζ ^ (m + 1) * a4) * τ := by sorry
