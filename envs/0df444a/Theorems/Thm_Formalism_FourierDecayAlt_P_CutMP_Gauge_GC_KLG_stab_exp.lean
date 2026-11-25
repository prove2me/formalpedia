-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_KLG_stab_exp
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLG.stab_exp
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:17:29.354213+00:00
-- url     : https://prove2.me/theorems/d02d23b2-2538-4af9-a68a-054981f726db
-- title:
--   KLG: stab exp
-- statement:
--   The KLG construction uses the stab exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreKLLieGrpGeo.lean#L48-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreKLLieGrpGeo.lean#L48-L118

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormRankFour
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExistsFrameTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreKLLieGrpGeo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLG
open Formalism.FourierDecayAlt.P.HermitianFormRankFour
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLG.stab_exp {z e : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (he : inWb k r e)
    (hez : herm (Hpk k r) e z = 0) (hee : herm (Hpk k r) e e = 1) {Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ}
    (hB : IsFrameOf k r [z, e] Bs) {h : Mx k r} (hh : h ∈ UWset k r z) (hhe : h *ᵥ e = e) :
    ∃ B : Matrix (Fin (k - 1)) (Fin (k - 1)) ℂ, Bᴴ = -B ∧
      NormedSpace.exp (colM Bs * B * ((colM Bs)ᴴ * Hpk k r)) = h := by sorry
