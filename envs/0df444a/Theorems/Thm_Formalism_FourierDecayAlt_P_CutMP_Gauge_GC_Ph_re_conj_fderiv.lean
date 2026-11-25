-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ph_re_conj_fderiv
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph.re_conj_fderiv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:13:01.564904+00:00
-- url     : https://prove2.me/theorems/175e195e-f58f-56fa-b214-50144f3eba70
-- title:
--   Ph: re conj fderiv
-- statement:
--   The Ph construction uses the re conj fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCHolPh.lean#L18-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCHolPh.lean#L18-L35

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCHolPh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph.re_conj_fderiv {TT : ℝ} {u : ℂ → ℂ} (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (AnnT TT))
    (h1 : ∀ ζ ∈ AnnT TT, ‖u ζ‖ = 1) {ζ : ℂ} (hζ : ζ ∈ AnnT TT) (h : ℂ) :
    (star (u ζ) * fderiv ℝ u ζ h).re = 0 := by sorry
