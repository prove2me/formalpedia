-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_keyV
-- name    : Formalism.FourierDecayAlt.P.RuleGD.keyV
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:06:08.33349+00:00
-- url     : https://prove2.me/theorems/4c8e59a7-23bb-4fbf-add6-b0fc524da3d2
-- title:
--   Rule GD: key V
-- statement:
--   The Rule GD construction uses the key V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleGD.lean#L136-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleGD.lean#L136-L167

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleGD
open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Matrix
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

theorem Formalism.FourierDecayAlt.P.RuleGD.keyV (L : LevelData A r) (φ : A →+* A) (t : ℂ) (e : A)
    (hal : ∀ z, φ (algebraMap ℂ A z) = algebraMap ℂ A z)
    (hpb : ∀ l, φ (L.pb l) = L.pb l + algebraMap ℂ A t)
    (hcb : ∀ l, φ (L.cb l) = L.cb l) (hcbi : ∀ l, φ (L.cbi l) = L.cbi l)
    (hc : ∀ l, φ (L.c l) = L.c l) (hGG : φ L.GG = L.GG) (hz : φ L.ζ = L.ζ)
    (hGGi : φ L.GGi = L.GGi)
    (hnabs : φ L.nabs = L.nabs - algebraMap ℂ A t * (L.ζ * L.GGi) - e) (Y : ℂ) :
    φ (L.Ahatv Y) = L.Ahatv (Y - t) ∧
      φ (L.R0v Y) = L.R0v (Y - t) + L.Dr * L.GG * e * L.Avr (Y - t) := by sorry
