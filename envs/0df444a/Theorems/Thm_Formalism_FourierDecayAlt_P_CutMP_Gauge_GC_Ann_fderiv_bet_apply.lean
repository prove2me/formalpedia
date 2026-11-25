-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_fderiv_bet_apply
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.fderiv_bet_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:12:14.376342+00:00
-- url     : https://prove2.me/theorems/9e981849-57c1-470c-8890-7561cf976d50
-- title:
--   Ann: fderiv bet apply
-- statement:
--   The Ann construction uses the fderiv bet apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BasePointMemHalfPlane.lean#L42-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BasePointMemHalfPlane.lean#L42-L68

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FderivDecomp
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BasePointMemHalfPlane
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {TT : ℝ} {α : ℂ → ℂ}

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.fderiv_bet_apply (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) {w : ℂ} (hw : w ∈ Hh TT) (v : ℂ) :
    fderiv ℝ (bet α) w v = (α (Complex.exp w) * Complex.exp w + wZ α (Complex.exp w) * Complex.exp w ^ 2) * v +
      wZb α (Complex.exp w) * Complex.exp w * (starRingEnd ℂ) (Complex.exp w) * (starRingEnd ℂ) v := by sorry
