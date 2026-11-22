-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_keyA
-- name    : Formalism.FourierDecayAlt.P.RuleGD.keyA
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:06:04.617821+00:00
-- url     : https://prove2.me/theorems/c662768c-fabc-4219-a70a-283ec0742382
-- title:
--   Rule GD: key A
-- statement:
--   The Rule GD construction uses the key A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleGD.lean#L103-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleGD.lean#L103-L134

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

theorem Formalism.FourierDecayAlt.P.RuleGD.keyA (L : LevelData A r) (φ : A →+* A) (t : ℂ) (e : A)
    (hal : ∀ z, φ (algebraMap ℂ A z) = algebraMap ℂ A z)
    (hp : ∀ l, φ (L.p l) = L.p l + algebraMap ℂ A t)
    (hc : ∀ l, φ (L.c l) = L.c l) (hci : ∀ l, φ (L.ci l) = L.ci l)
    (hcb : ∀ l, φ (L.cb l) = L.cb l) (hGG : φ L.GG = L.GG) (hzb : φ L.ζb = L.ζb)
    (hGGi : φ L.GGi = L.GGi)
    (hnab : φ L.nab = L.nab + algebraMap ℂ A t * (L.ζb * L.GGi) - e) (Y : ℂ) :
    φ (L.Ahat Y) = L.Ahat (Y + t) ∧
      φ (L.R0 Y) = L.R0 (Y + t) + L.Drb * L.GG * e * L.Ar (Y + t) := by sorry
