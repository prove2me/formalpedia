-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_four_inter
-- name    : Formalism.FourierDecayAlt.P.RuleSS.four_inter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:25.420303+00:00
-- url     : https://prove2.me/theorems/ed3c573e-8b1e-4de4-a0e9-b87adac54f91
-- title:
--   Rule SS: four inter
-- statement:
--   The Rule SS construction uses the four inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleSS.lean#L166-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleSS.lean#L166-L177

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleSS
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
variable {r : ℕ} (L : LevelData A r)

theorem Formalism.FourierDecayAlt.P.RuleSS.four_inter (h : A) (Ya Y1 Yl Yl' Yv Yv' Ym Ym' : ℂ)
    (hA : L.Ar Ya * h = h * L.Ar Y1) (hB : L.Br Ya * h = h * L.Br Y1)
    (hl : L.l0 Yl * h = h * L.l0 Yl')
    (hAv : L.Avr Yv * h = h * L.Avr Yv') (hBv : L.Bvr Yv * h = h * L.Bvr Yv')
    (hm : L.m0 Ym * h = h * L.m0 Ym')
    (hDr : Commute L.Dr h) (hDrb : Commute L.Drb h) (hGG : Commute L.GG h) :
    L.Dr * L.Ar Ya * h = h * (L.Dr * L.Ar Y1) ∧
    L.Drb * L.GG * (L.l0 Yl * L.Ar Ya + L.Br Ya) * h = h * (L.Drb * L.GG * (L.l0 Yl' * L.Ar Y1 + L.Br Y1)) ∧
    L.Drb * L.Avr Yv * h = h * (L.Drb * L.Avr Yv') ∧
    L.Dr * L.GG * (L.m0 Ym * L.Avr Yv + L.Bvr Yv) * h = h * (L.Dr * L.GG * (L.m0 Ym' * L.Avr Yv' + L.Bvr Yv')) := by sorry
